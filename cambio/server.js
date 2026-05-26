const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const PEEK_DURATION = 8000;
const SNAP_WINDOW_DURATION = 5000;
const RECONNECT_GRACE_PERIOD = 60000;
const POWER_PEEK_DURATION = 3000;

const MIME_TYPES = {
  '.html': 'text/html',
  '.js': 'application/javascript',
  '.css': 'text/css',
  '.json': 'application/json',
  '.png': 'image/png',
  '.ico': 'image/x-icon',
};

const rooms = new Map();
const clientToRoom = new Map();

const SUITS = ['hearts', 'diamonds', 'clubs', 'spades'];
const RANKS = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K'];

function cardValue(rank) {
  if (rank === 'Joker') return 0;
  if (rank === 'A') return 1;
  if (rank === 'J') return 11;
  if (rank === 'Q') return 12;
  if (rank === 'K') return 13;
  return parseInt(rank, 10);
}

function buildDeck() {
  const deck = [];
  for (const suit of SUITS) {
    for (const rank of RANKS) {
      deck.push({ suit, rank, value: cardValue(rank) });
    }
  }
  deck.push({ suit: 'joker', rank: 'Joker', value: 0 });
  deck.push({ suit: 'joker', rank: 'Joker', value: 0 });
  return deck;
}

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function generateRoomCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
  let code;
  do {
    code = '';
    for (let i = 0; i < 4; i++) code += chars[Math.floor(Math.random() * chars.length)];
  } while (rooms.has(code));
  return code;
}

function send(ws, type, data = {}) {
  if (ws && ws.readyState === 1) {
    ws.send(JSON.stringify({ type, ...data }));
  }
}

function sendError(ws, message) {
  send(ws, 'error', { message });
}

function opponentOf(i) { return i === 0 ? 1 : 0; }

function playerByWs(game, ws) {
  return game.players.findIndex(p => p.ws === ws);
}

function drawFromDeck(game) {
  if (game.deck.length === 0) {
    if (game.discardPile.length <= 1) return null;
    const top = game.discardPile.pop();
    game.deck = shuffle(game.discardPile);
    game.discardPile = [top];
  }
  return game.deck.pop();
}

function topDiscard(game) {
  return game.discardPile.length > 0 ? game.discardPile[game.discardPile.length - 1] : null;
}

function scoreHand(hand) {
  return hand.reduce((sum, c) => sum + (c ? c.value : 0), 0);
}

function activeHandSize(hand) {
  return hand.filter(c => c !== null).length;
}

function c(card) {
  return { suit: card.suit, rank: card.rank, value: card.value };
}

function cleanupRoom(roomCode) {
  const game = rooms.get(roomCode);
  if (!game) return;
  for (const t of [game.snapTimeout, game.peekTimeout, game.disconnectTimeout, game.powerPeekTimeout]) {
    if (t) clearTimeout(t);
  }
  for (const p of game.players) {
    if (p.clientId) clientToRoom.delete(p.clientId);
  }
  rooms.delete(roomCode);
}

function getPower(card, mode = 'classic') {
  if (mode === 'steroids') {
    if (card.rank === 'A') return 'ace_peek_all';
    if (card.rank === 'Joker') return 'joker_discard2';
    if (card.rank === '2') return 'steal';
    if (card.rank === '3') return 'give';
    if (card.rank === '4') return 'deck_give';
    if (card.rank === '5') return 'self_draw';
    if (card.rank === '6') return 'skip';
    if (card.rank === 'J') return 'jack_peek_both';
  }
  if (card.rank === '7' || card.rank === '8') return 'peek_own';
  if (card.rank === '9' || card.rank === '10') return 'peek_opponent';
  if (card.rank === 'J' || card.rank === 'Q') return 'blind_swap';
  if (card.rank === 'K') return 'king';
  return null;
}

function powerToClientName(power) {
  if (power === 'peek_own') return '7_8';
  if (power === 'peek_opponent') return '9_10';
  if (power === 'blind_swap') return 'JQ';
  if (power === 'king') return 'K';
  if (power === 'ace_peek_all') return 'A_peek_all';
  if (power === 'joker_discard2') return 'JKR_discard2';
  if (power === 'steal') return '2_steal';
  if (power === 'give') return '3_give';
  if (power === 'deck_give') return '4_deck_give';
  if (power === 'self_draw') return '5_self_draw';
  if (power === 'skip') return '6_skip';
  if (power === 'jack_peek_both') return 'J_peek_both';
  return null;
}

// --- Game flow ---

function dealAndWaitForReady(game) {
  game.deck = shuffle(buildDeck());
  game.discardPile = [];
  game.currentTurn = 0;
  game.turnPhase = 'waiting_for_draw';
  game.drawnCard = null;
  game.cambioCallerIndex = null;
  game.turnsRemaining = null;
  game.snapWindow = false;
  game.snapTimeout = null;
  game.powerContext = null;
  game.powerPeekTimeout = null;
  game.skipNextTurn = false;
  game.readyPlayers = new Set();

  for (const p of game.players) {
    p.hand = [];
    for (let i = 0; i < 4; i++) {
      p.hand.push(game.deck.pop());
    }
  }

  const firstDiscard = game.deck.pop();
  game.discardPile.push(firstDiscard);
  game.state = 'waiting_ready';

  for (let i = 0; i < game.players.length; i++) {
    const p = game.players[i];
    const op = game.players[opponentOf(i)];
    send(p.ws, 'game_start', {
      yourIndex: i,
      mode: game.mode,
      opponentHandSize: op.hand.length,
      topDiscard: c(firstDiscard),
      cardsRemaining: game.deck.length,
      needsReady: true,
    });
  }
}

function handleReady(game, pi) {
  if (game.state !== 'waiting_ready') return;
  game.readyPlayers.add(pi);

  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, 'player_ready', {
      player: i === pi ? 'self' : 'opponent',
      allReady: game.readyPlayers.size >= 2,
    });
  }

  if (game.readyPlayers.size >= 2) {
    startPeek(game);
  }
}

function startPeek(game) {
  game.state = 'peek';

  for (let i = 0; i < game.players.length; i++) {
    const p = game.players[i];
    send(p.ws, 'initial_peek', {
      cards: [
        { index: 0, card: c(p.hand[0]) },
        { index: 3, card: c(p.hand[3]) },
      ],
      duration: PEEK_DURATION,
    });
  }

  game.peekTimeout = setTimeout(() => {
    game.peekTimeout = null;
    game.state = 'playing';
    for (const p of game.players) {
      send(p.ws, 'peek_end', {});
    }
    notifyTurn(game);
  }, PEEK_DURATION);
}

function notifyTurn(game) {
  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, i === game.currentTurn ? 'your_turn' : 'opponent_turn', {});
  }
}

function advanceTurn(game) {
  if (game.state === 'game_over') return;

  if (game.turnsRemaining !== null) {
    game.turnsRemaining--;
    if (game.turnsRemaining <= 0) {
      endGame(game);
      return;
    }
  }

  game.currentTurn = opponentOf(game.currentTurn);
  game.turnPhase = 'waiting_for_draw';
  game.drawnCard = null;
  game.powerContext = null;

  if (game.skipNextTurn) {
    game.skipNextTurn = false;
    for (let i = 0; i < game.players.length; i++) {
      send(game.players[i].ws, 'turn_skipped', {
        player: i === game.currentTurn ? 'self' : 'opponent',
      });
    }
    advanceTurn(game);
    return;
  }

  notifyTurn(game);
}

function openSnapWindow(game) {
  game.snapWindow = true;
  const td = topDiscard(game);
  for (const p of game.players) {
    send(p.ws, 'snap_window', { open: true, topDiscard: td ? c(td) : null });
  }
  game.snapTimeout = setTimeout(() => closeSnapWindow(game), SNAP_WINDOW_DURATION);
}

function closeSnapWindow(game) {
  if (!game.snapWindow) return;
  game.snapWindow = false;
  if (game.snapTimeout) {
    clearTimeout(game.snapTimeout);
    game.snapTimeout = null;
  }
  for (const p of game.players) {
    send(p.ws, 'snap_window', { open: false });
  }
  advanceTurn(game);
}

function discardAndProcess(game, card) {
  game.discardPile.push(card);
  game.drawnCard = null;

  const power = getPower(card, game.mode);

  for (const p of game.players) {
    send(p.ws, 'card_discarded', {
      card: c(card),
      cardsRemaining: game.deck.length,
    });
  }

  if (power) {
    const pi = game.currentTurn;
    const oi = opponentOf(pi);

    if (power === 'deck_give') {
      const drawn = drawFromDeck(game);
      if (drawn) {
        game.players[oi].hand.push(drawn);
      }
      for (let i = 0; i < game.players.length; i++) {
        send(game.players[i].ws, 'deck_give_done', {
          player: i === pi ? 'self' : 'opponent',
          newMyHandSize: game.players[i].hand.length,
          newOppHandSize: game.players[opponentOf(i)].hand.length,
        });
      }
      openSnapWindow(game);
      return;
    }

    if (power === 'self_draw') {
      const drawn = drawFromDeck(game);
      if (drawn) {
        game.players[pi].hand.push(drawn);
      }
      for (let i = 0; i < game.players.length; i++) {
        send(game.players[i].ws, 'self_draw_done', {
          player: i === pi ? 'self' : 'opponent',
          newMyHandSize: game.players[i].hand.length,
          newOppHandSize: game.players[opponentOf(i)].hand.length,
        });
      }
      openSnapWindow(game);
      return;
    }

    if (power === 'skip') {
      game.skipNextTurn = true;
      for (let i = 0; i < game.players.length; i++) {
        send(game.players[i].ws, 'skip_done', {
          player: i === pi ? 'self' : 'opponent',
        });
      }
      openSnapWindow(game);
      return;
    }

    if (power === 'ace_peek_all') {
      const allCards = [];
      for (let i = 0; i < game.players.length; i++) {
        const label = i === pi ? 'self' : 'opponent';
        for (let j = 0; j < game.players[i].hand.length; j++) {
          if (game.players[i].hand[j] === null) continue;
          allCards.push({ owner: label, index: j, card: c(game.players[i].hand[j]) });
        }
      }
      send(game.players[pi].ws, 'peek_all_result', {
        cards: allCards,
        duration: PEEK_DURATION,
      });
      send(game.players[oi].ws, 'power_activate', {
        power: powerToClientName(power),
      });
      game.powerPeekTimeout = setTimeout(() => {
        game.powerPeekTimeout = null;
        finishPowerAndSnap(game);
      }, PEEK_DURATION);
      return;
    }

    if (power === 'joker_discard2') {
      const selectionsLeft = Math.min(2, activeHandSize(game.players[pi].hand));
      game.powerContext = { power, card, selectionsLeft };
      game.turnPhase = 'power_joker_discard2';
      send(game.players[pi].ws, 'power_activate', {
        power: powerToClientName(power),
        selectionsLeft,
      });
      return;
    }

    game.turnPhase = 'power_' + power;
    game.powerContext = { power, card, step: power === 'jack_peek_both' ? 'self' : undefined };
    send(game.players[game.currentTurn].ws, 'power_activate', {
      power: powerToClientName(power),
    });
  } else {
    openSnapWindow(game);
  }
}

function finishPowerAndSnap(game) {
  game.turnPhase = 'waiting_for_draw';
  game.powerContext = null;
  openSnapWindow(game);
}

function endGame(game) {
  game.state = 'game_over';
  if (game.snapTimeout) { clearTimeout(game.snapTimeout); game.snapTimeout = null; }
  if (game.powerPeekTimeout) { clearTimeout(game.powerPeekTimeout); game.powerPeekTimeout = null; }

  const scores = game.players.map(p => scoreHand(p.hand));
  let callerPenalty = false;

  if (game.cambioCallerIndex !== null) {
    const cs = scores[game.cambioCallerIndex];
    const os = scores[opponentOf(game.cambioCallerIndex)];
    if (cs >= os) {
      scores[game.cambioCallerIndex] += 10;
      callerPenalty = true;
    }
  }

  for (let i = 0; i < game.players.length; i++) {
    const opIdx = opponentOf(i);
    let winner;
    if (scores[i] < scores[opIdx]) winner = 'self';
    else if (scores[opIdx] < scores[i]) winner = 'opponent';
    else winner = 'tie';

    send(game.players[i].ws, 'game_over', {
      myScore: scores[i],
      opponentScore: scores[opIdx],
      winner,
      callerPenalty,
      myCards: game.players[i].hand.filter(x => x).map(c),
      opponentCards: game.players[opIdx].hand.filter(x => x).map(c),
    });
  }
}

// --- Message handlers ---

function handleCreateRoom(ws, data) {
  const playerName = (data.playerName || '').trim();
  if (!playerName || playerName.length > 20) return sendError(ws, 'Invalid player name');

  const mode = data.mode === 'steroids' ? 'steroids' : 'classic';
  const roomCode = generateRoomCode();
  const clientId = crypto.randomUUID();

  const game = {
    roomCode, state: 'lobby', mode,
    players: [{ ws, name: playerName, hand: [], connected: true, clientId }],
    deck: [], discardPile: [], currentTurn: 0,
    turnPhase: 'waiting_for_draw', drawnCard: null,
    cambioCallerIndex: null, turnsRemaining: null,
    snapWindow: false, snapTimeout: null, peekTimeout: null,
    disconnectTimeout: null, powerContext: null, powerPeekTimeout: null,
    skipNextTurn: false, readyPlayers: new Set(),
  };

  rooms.set(roomCode, game);
  clientToRoom.set(clientId, roomCode);
  send(ws, 'room_created', { roomCode, clientId, playerIndex: 0, mode });
}

function handleJoinRoom(ws, data) {
  const playerName = (data.playerName || '').trim();
  if (!playerName || playerName.length > 20) return sendError(ws, 'Invalid player name');

  const roomCode = (data.roomCode || '').toUpperCase().trim();
  const game = rooms.get(roomCode);
  if (!game) return sendError(ws, 'Room not found');
  if (game.state !== 'lobby') return sendError(ws, 'Game already in progress');
  if (game.players.length >= 2) return sendError(ws, 'Room is full');

  const clientId = crypto.randomUUID();
  game.players.push({ ws, name: playerName, hand: [], connected: true, clientId });
  clientToRoom.set(clientId, roomCode);

  send(ws, 'room_joined', {
    roomCode, clientId, playerIndex: 1,
    opponentName: game.players[0].name,
    mode: game.mode,
  });
  send(game.players[0].ws, 'player_joined', { playerName });

  dealAndWaitForReady(game);
}

function handleReconnect(ws, data) {
  const clientId = data.clientId;
  if (!clientId) return sendError(ws, 'Missing clientId');

  const roomCode = clientToRoom.get(clientId);
  if (!roomCode) return sendError(ws, 'Session expired');

  const game = rooms.get(roomCode);
  if (!game) { clientToRoom.delete(clientId); return sendError(ws, 'Room gone'); }

  const pi = game.players.findIndex(p => p.clientId === clientId);
  if (pi === -1) return sendError(ws, 'Player not found');

  game.players[pi].ws = ws;
  game.players[pi].connected = true;

  if (game.disconnectTimeout) { clearTimeout(game.disconnectTimeout); game.disconnectTimeout = null; }

  const oi = opponentOf(pi);
  if (game.players[oi]) send(game.players[oi].ws, 'opponent_reconnected', {});

  const p = game.players[pi];
  const op = game.players[oi];

  send(ws, 'reconnect_success', {
    gamePhase: game.state,
    playerIndex: pi,
    mode: game.mode,
    opponentName: op ? op.name : 'Opponent',
    isMyTurn: game.currentTurn === pi,
    turnPhase: game.currentTurn === pi ? game.turnPhase : null,
    myHand: p.hand.map(c => ({ removed: c === null })),
    opponentHand: op ? op.hand.map(c => ({ removed: c === null })) : [],
    topDiscard: topDiscard(game) ? c(topDiscard(game)) : null,
    cardsRemaining: game.deck.length,
  });
}

function handleDraw(game, pi, source) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'waiting_for_draw') return sendError(p.ws, 'Cannot draw now');

  if (source === 'discard') {
    if (game.discardPile.length === 0) return sendError(p.ws, 'Discard pile is empty');
    const card = game.discardPile.pop();
    game.drawnCard = card;
    game.turnPhase = 'drawn_from_discard';

    send(p.ws, 'card_drawn', { source: 'discard', card: c(card), cardsRemaining: game.deck.length });
    send(game.players[opponentOf(pi)].ws, 'opponent_drew', { source: 'discard', cardsRemaining: game.deck.length });
  } else {
    const card = drawFromDeck(game);
    if (!card) return sendError(p.ws, 'No cards available');
    game.drawnCard = card;
    game.turnPhase = 'drawn_from_pile';

    send(p.ws, 'card_drawn', { source: 'pile', card: c(card), cardsRemaining: game.deck.length });
    send(game.players[opponentOf(pi)].ws, 'opponent_drew', { source: 'pile', cardsRemaining: game.deck.length });
  }
}

function handleSwap(game, pi, handIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'drawn_from_pile' && game.turnPhase !== 'drawn_from_discard') {
    return sendError(p.ws, 'Cannot swap now');
  }
  if (!Number.isInteger(handIndex) || handIndex < 0 || handIndex >= p.hand.length || p.hand[handIndex] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  const oldCard = p.hand[handIndex];
  p.hand[handIndex] = game.drawnCard;
  game.discardPile.push(oldCard);
  game.drawnCard = null;
  game.turnPhase = 'waiting_for_draw';

  const oi = opponentOf(pi);
  send(p.ws, 'card_swapped', {
    player: 'self', index: handIndex,
    discardedCard: c(oldCard),
  });
  send(game.players[oi].ws, 'card_swapped', {
    player: 'opponent', index: handIndex,
    discardedCard: c(oldCard),
  });

  openSnapWindow(game);
}

function handleDiscardDrawn(game, pi) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'drawn_from_pile') return sendError(p.ws, 'Can only discard from draw pile');
  if (!game.drawnCard) return sendError(p.ws, 'No drawn card');
  discardAndProcess(game, game.drawnCard);
}

function handlePeekOwn(game, pi, handIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_peek_own') return sendError(p.ws, 'Cannot peek now');
  if (!Number.isInteger(handIndex) || handIndex < 0 || handIndex >= p.hand.length || p.hand[handIndex] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  send(p.ws, 'peek_result', {
    target: 'self', index: handIndex,
    card: c(p.hand[handIndex]),
    duration: POWER_PEEK_DURATION,
  });

  game.powerPeekTimeout = setTimeout(() => {
    game.powerPeekTimeout = null;
    finishPowerAndSnap(game);
  }, POWER_PEEK_DURATION);
}

function handlePeekOpponent(game, pi, handIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_peek_opponent') return sendError(p.ws, 'Cannot peek now');

  const oi = opponentOf(pi);
  if (!Number.isInteger(handIndex) || handIndex < 0 || handIndex >= game.players[oi].hand.length || game.players[oi].hand[handIndex] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  send(p.ws, 'peek_result', {
    target: 'opponent', index: handIndex,
    card: c(game.players[oi].hand[handIndex]),
    duration: POWER_PEEK_DURATION,
  });

  game.powerPeekTimeout = setTimeout(() => {
    game.powerPeekTimeout = null;
    finishPowerAndSnap(game);
  }, POWER_PEEK_DURATION);
}

function handleBlindSwap(game, pi, myIndex, oppIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_blind_swap') return sendError(p.ws, 'Cannot swap now');

  const oi = opponentOf(pi);
  const op = game.players[oi];

  if (!Number.isInteger(myIndex) || myIndex < 0 || myIndex >= p.hand.length || p.hand[myIndex] === null) return sendError(p.ws, 'Invalid index');
  if (!Number.isInteger(oppIndex) || oppIndex < 0 || oppIndex >= op.hand.length || op.hand[oppIndex] === null) return sendError(p.ws, 'Invalid opponent index');

  [p.hand[myIndex], op.hand[oppIndex]] = [op.hand[oppIndex], p.hand[myIndex]];

  send(p.ws, 'power_swap_done', { myIndex, oppIndex });
  send(op.ws, 'power_swap_done', { myIndex: oppIndex, oppIndex: myIndex });

  finishPowerAndSnap(game);
}

function handleKingLook(game, pi, oppIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_king') return sendError(p.ws, 'Cannot look now');

  const oi = opponentOf(pi);
  if (!Number.isInteger(oppIndex) || oppIndex < 0 || oppIndex >= game.players[oi].hand.length || game.players[oi].hand[oppIndex] === null) {
    return sendError(p.ws, 'Invalid opponent index');
  }

  game.powerContext.lookedIndex = oppIndex;
  game.turnPhase = 'power_king_decide';

  send(p.ws, 'king_peek_result', {
    card: c(game.players[oi].hand[oppIndex]),
    index: oppIndex,
    duration: 5000,
  });
}

function handleKingDecide(game, pi, doSwap, myIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_king_decide') return sendError(p.ws, 'Cannot decide now');

  const oi = opponentOf(pi);
  const oppCardIdx = game.powerContext.lookedIndex;

  if (doSwap) {
    if (!Number.isInteger(myIndex) || myIndex < 0 || myIndex >= p.hand.length || p.hand[myIndex] === null) {
      return sendError(p.ws, 'Invalid hand index');
    }
    [p.hand[myIndex], game.players[oi].hand[oppCardIdx]] = [game.players[oi].hand[oppCardIdx], p.hand[myIndex]];

    send(p.ws, 'king_swap_done', { myIndex, oppIndex: oppCardIdx });
    send(game.players[oi].ws, 'king_swap_done', { myIndex: oppCardIdx, oppIndex: myIndex });
  } else {
    send(p.ws, 'king_swap_done', { swapped: false });
  }

  finishPowerAndSnap(game);
}

function handleSnap(game, pi, handIndex, targetPlayer) {
  const p = game.players[pi];
  if (!game.snapWindow) return sendError(p.ws, 'No snap window');

  const target = targetPlayer === 'opponent' ? opponentOf(pi) : pi;
  const targetHand = game.players[target].hand;

  if (!Number.isInteger(handIndex) || handIndex < 0 || handIndex >= targetHand.length || targetHand[handIndex] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  const td = topDiscard(game);
  if (!td) return sendError(p.ws, 'No discard');

  const snappedCard = targetHand[handIndex];
  const success = snappedCard.value === td.value;

  if (success) {
    targetHand[handIndex] = null;
    game.discardPile.push(snappedCard);

    for (let i = 0; i < game.players.length; i++) {
      send(game.players[i].ws, 'snap_result', {
        success: true,
        player: i === pi ? 'self' : 'opponent',
        targetPlayer: i === target ? 'self' : 'opponent',
        index: handIndex,
        card: c(snappedCard),
        topDiscard: topDiscard(game) ? c(topDiscard(game)) : null,
      });
    }

    if (activeHandSize(targetHand) === 0) {
      if (game.snapTimeout) { clearTimeout(game.snapTimeout); game.snapTimeout = null; }
      game.snapWindow = false;
      endGame(game);
      return;
    }
  } else {
    const penalty = drawFromDeck(game);
    if (penalty) p.hand.push(penalty);

    for (let i = 0; i < game.players.length; i++) {
      send(game.players[i].ws, 'snap_result', {
        success: false,
        player: i === pi ? 'self' : 'opponent',
        targetPlayer: i === target ? 'self' : 'opponent',
        index: handIndex,
        card: c(snappedCard),
        penaltyIndex: penalty ? p.hand.length - 1 : null,
        topDiscard: topDiscard(game) ? c(topDiscard(game)) : null,
      });
    }
  }
}

function handleCallCambio(game, pi) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'waiting_for_draw') return sendError(p.ws, 'Cannot call Cambio now');
  if (game.cambioCallerIndex !== null) return sendError(p.ws, 'Cambio already called');

  game.cambioCallerIndex = pi;
  game.state = 'cambio_round';
  game.turnsRemaining = 1;

  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, 'cambio_called', {
      player: i === pi ? 'self' : 'opponent',
    });
  }

  game.currentTurn = opponentOf(pi);
  game.turnPhase = 'waiting_for_draw';
  game.drawnCard = null;
  game.powerContext = null;

  send(game.players[opponentOf(pi)].ws, 'final_turn', {});
  notifyTurn(game);
}

function handlePlayAgain(game, ws) {
  if (game.state !== 'game_over') return sendError(ws, 'Game is not over');
  if (!game._playAgainVotes) game._playAgainVotes = new Set();
  const pi = playerByWs(game, ws);
  if (pi === -1) return;
  game._playAgainVotes.add(pi);
  if (game._playAgainVotes.size >= 2) {
    game._playAgainVotes = null;
    dealAndWaitForReady(game);
  }
}

function handleJokerSelect(game, pi, index) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_joker_discard2') return sendError(p.ws, 'Cannot discard now');
  if (!Number.isInteger(index) || index < 0 || index >= p.hand.length || p.hand[index] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  const removed = p.hand[index];
  p.hand[index] = null;
  game.discardPile.push(removed);
  game.powerContext.selectionsLeft--;

  const oi = opponentOf(pi);
  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, 'joker_card_removed', {
      player: i === pi ? 'self' : 'opponent',
      index,
      card: c(removed),
      remainingSelections: game.powerContext.selectionsLeft,
    });
  }

  if (game.powerContext.selectionsLeft <= 0 || activeHandSize(p.hand) === 0) {
    finishPowerAndSnap(game);
    return;
  }
}

function handleSteal(game, pi, oppIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_steal') return sendError(p.ws, 'Cannot steal now');

  const oi = opponentOf(pi);
  const op = game.players[oi];
  if (!Number.isInteger(oppIndex) || oppIndex < 0 || oppIndex >= op.hand.length || op.hand[oppIndex] === null) {
    return sendError(p.ws, 'Invalid opponent index');
  }

  const stolen = op.hand[oppIndex];
  op.hand[oppIndex] = null;
  p.hand.push(stolen);

  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, 'steal_done', {
      player: i === pi ? 'self' : 'opponent',
      oppIndex,
      newMyHandSize: game.players[i].hand.length,
      newOppHandSize: game.players[opponentOf(i)].hand.length,
    });
  }

  finishPowerAndSnap(game);
}

function handleGive(game, pi, myIndex) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_give') return sendError(p.ws, 'Cannot give now');

  if (!Number.isInteger(myIndex) || myIndex < 0 || myIndex >= p.hand.length || p.hand[myIndex] === null) {
    return sendError(p.ws, 'Invalid hand index');
  }

  const oi = opponentOf(pi);
  const given = p.hand[myIndex];
  p.hand[myIndex] = null;
  game.players[oi].hand.push(given);

  for (let i = 0; i < game.players.length; i++) {
    send(game.players[i].ws, 'give_done', {
      player: i === pi ? 'self' : 'opponent',
      myIndex,
      newMyHandSize: game.players[i].hand.length,
      newOppHandSize: game.players[opponentOf(i)].hand.length,
    });
  }

  finishPowerAndSnap(game);
}

function handleJackPeekBoth(game, pi, target, index) {
  const p = game.players[pi];
  if (game.currentTurn !== pi) return sendError(p.ws, 'Not your turn');
  if (game.turnPhase !== 'power_jack_peek_both') return sendError(p.ws, 'Cannot peek now');

  const ctx = game.powerContext;

  if (ctx.step === 'self' && target === 'self') {
    if (!Number.isInteger(index) || index < 0 || index >= p.hand.length || p.hand[index] === null) {
      return sendError(p.ws, 'Invalid hand index');
    }
    send(p.ws, 'peek_result', {
      target: 'self', index, card: c(p.hand[index]), duration: POWER_PEEK_DURATION,
    });
    ctx.step = 'opp';
    send(p.ws, 'jack_peek_step', { step: 'opp' });
    return;
  }

  if (ctx.step === 'opp' && target === 'opponent') {
    const oi = opponentOf(pi);
    if (!Number.isInteger(index) || index < 0 || index >= game.players[oi].hand.length || game.players[oi].hand[index] === null) {
      return sendError(p.ws, 'Invalid opponent index');
    }
    send(p.ws, 'peek_result', {
      target: 'opponent', index, card: c(game.players[oi].hand[index]), duration: POWER_PEEK_DURATION,
    });
    game.powerPeekTimeout = setTimeout(() => {
      game.powerPeekTimeout = null;
      finishPowerAndSnap(game);
    }, POWER_PEEK_DURATION);
    return;
  }

  return sendError(p.ws, 'Invalid target for this step');
}

function handleDisconnect(ws) {
  let foundGame = null;
  let foundPI = -1;

  for (const [, game] of rooms) {
    const idx = game.players.findIndex(p => p.ws === ws);
    if (idx !== -1) { foundGame = game; foundPI = idx; break; }
  }
  if (!foundGame) return;

  foundGame.players[foundPI].connected = false;
  foundGame.players[foundPI].ws = null;

  if (foundGame.state === 'lobby') { cleanupRoom(foundGame.roomCode); return; }

  const oi = opponentOf(foundPI);
  if (foundGame.players[oi] && foundGame.players[oi].connected) {
    send(foundGame.players[oi].ws, 'opponent_disconnected', {});
  }

  const bothGone = foundGame.players.every(p => !p.connected);
  foundGame.disconnectTimeout = setTimeout(() => {
    if (bothGone) cleanupRoom(foundGame.roomCode);
    else if (foundGame.state !== 'game_over') endGame(foundGame);
  }, RECONNECT_GRACE_PERIOD);
}

// --- Message router ---

function handleMessage(ws, raw) {
  let msg;
  try { msg = JSON.parse(raw); } catch { return sendError(ws, 'Invalid JSON'); }

  const { type } = msg;

  if (type === 'create_room') return handleCreateRoom(ws, msg);
  if (type === 'join_room') return handleJoinRoom(ws, msg);
  if (type === 'reconnect') return handleReconnect(ws, msg);

  let game = null;
  let pi = -1;
  for (const [, g] of rooms) {
    const idx = g.players.findIndex(p => p.ws === ws);
    if (idx !== -1) { game = g; pi = idx; break; }
  }
  if (!game || pi === -1) return sendError(ws, 'Not in a game');

  if (type === 'play_again') return handlePlayAgain(game, ws);
  if (type === 'ready') return handleReady(game, pi);

  if (game.state !== 'playing' && game.state !== 'cambio_round') {
    return sendError(ws, 'Game is not in a playable state');
  }

  switch (type) {
    case 'draw':
      return handleDraw(game, pi, msg.source);
    case 'draw_pile':
      return handleDraw(game, pi, 'pile');
    case 'draw_discard':
      return handleDraw(game, pi, 'discard');
    case 'swap':
      return handleSwap(game, pi, msg.index);
    case 'swap_card':
      return handleSwap(game, pi, msg.handIndex);
    case 'discard_drawn':
      return handleDiscardDrawn(game, pi);
    case 'power_target':
      if (game.turnPhase === 'power_jack_peek_both') return handleJackPeekBoth(game, pi, msg.target, msg.index);
      if (msg.target === 'self') return handlePeekOwn(game, pi, msg.index);
      if (msg.target === 'opponent') return handlePeekOpponent(game, pi, msg.index);
      return sendError(ws, 'Invalid power target');
    case 'peek_own':
      return handlePeekOwn(game, pi, msg.handIndex);
    case 'peek_opponent':
      return handlePeekOpponent(game, pi, msg.handIndex);
    case 'power_swap':
      return handleBlindSwap(game, pi, msg.myIndex, msg.oppIndex);
    case 'blind_swap':
      return handleBlindSwap(game, pi, msg.myIndex, msg.opponentIndex);
    case 'king_peek':
      return handleKingLook(game, pi, msg.oppIndex);
    case 'king_look':
      return handleKingLook(game, pi, msg.opponentIndex);
    case 'king_swap':
      return handleKingDecide(game, pi, true, msg.myIndex);
    case 'king_keep':
      return handleKingDecide(game, pi, false);
    case 'king_decide':
      return handleKingDecide(game, pi, msg.doSwap, msg.myIndex);
    case 'snap':
      return handleSnap(game, pi, msg.index !== undefined ? msg.index : msg.handIndex, msg.target);
    case 'call_cambio':
      return handleCallCambio(game, pi);
    case 'joker_select':
      return handleJokerSelect(game, pi, msg.index);
    case 'steal_target':
      return handleSteal(game, pi, msg.index);
    case 'give_target':
      return handleGive(game, pi, msg.index);
    default:
      return sendError(ws, `Unknown message type: ${type}`);
  }
}

// --- HTTP server ---

const server = http.createServer((req, res) => {
  if (req.method !== 'GET') { res.writeHead(405); res.end('Method not allowed'); return; }

  let urlPath = req.url.split('?')[0];
  if (urlPath === '/') urlPath = '/index.html';

  const filePath = path.join(__dirname, 'public', urlPath);
  const resolved = path.resolve(filePath);
  const publicDir = path.resolve(path.join(__dirname, 'public'));

  if (!resolved.startsWith(publicDir)) { res.writeHead(403); res.end('Forbidden'); return; }

  fs.readFile(resolved, (err, data) => {
    if (err) { res.writeHead(404); res.end('Not found'); return; }
    const ext = path.extname(resolved).toLowerCase();
    res.writeHead(200, { 'Content-Type': MIME_TYPES[ext] || 'application/octet-stream' });
    res.end(data);
  });
});

const wss = new WebSocketServer({ server });

wss.on('connection', (ws) => {
  ws.on('message', (raw) => handleMessage(ws, raw.toString()));
  ws.on('close', () => handleDisconnect(ws));
  ws.on('error', () => handleDisconnect(ws));
});

server.listen(PORT, () => {
  console.log(`Cambio server running on port ${PORT}`);
});
