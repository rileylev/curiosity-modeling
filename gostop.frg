#lang forge

open "sigs.frg"
open "cards.frg"
open "score.frg"
open "turn_rules.frg"

pred initial[t: Turn] {
    all c: Card | c in t.deck -- all cards in deck
    all i: Int | no t.players[i] -- no players have any cards
    no t.table
    some t.deck -- deck should exist

    t.playing = 1 -- player 1 goes first
}

-- There should not be more than three players (at least in this version) during a turn
pred turnWellformed {
    all t: Turn | {
        #{i: Int | some t.players[i]} <= 3
    }
}

pred staysSameIfNotPrevPlaying[prev, post: Turn] {
    all j: Int | j != prev.playing implies {
        prev.players[j] = post.players[j]
    }
}

fun nextPlayer[prev: Turn]: Int {
    (prev.playing = 3) => 1 else add[prev.playing, 1]
}

pred nextTurn[prev, post: Turn] {
    -- Guard
    

    -- Action
    post.playing = nextPlayer[prev]
    -- If a card is gone from the deck, it must be with the player who played in the prev turn or on the table
    /* all c: Card | (c in prev.deck and not c in post.deck) implies { */
    /*     c in post.table or c in post.players[prev.playing] */
    /* } */
    // TODO: do we enforce hands are disjoint from each other + the table + the deck?
    one_player_go[prev.playing,
                  prev.players,
                  prev.stockpiles,
                  prev.table, prev.deck,
                  post.players,
                  post.stockpiles,
                  post.table, post.deck]

    -- Frame
    staysSameIfNotPrevPlaying[prev, post]
}

pred relaxed_traces {
    // cards are extensional
    no disj x,y : Card | {
        x.suit = y.suit
        x.month = y.month
    }
    // two turns
    some disj x,y : Turn | nextTurn[x,y]
}

run {
    relaxed_traces
} for exactly 20 Card for {next is linear}

pred traces {
    cardWellformed
    turnWellformed
    initial[Game.firstTurn]
    no prev: Turn | Game.next[prev] = Game.firstTurn

    all t: Turn | some Game.next[t] implies nextTurn[t, Game.next[t]]
}

run {
    traces
} for exactly 48 Card, exactly 3 Turn for { next is linear }
