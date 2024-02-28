#lang forge

open "cm.sigs.frg"
open "cm.cards.frg"
// open "cm.score.frg"

pred initial[t: Turn] {
    all c: Card | {
        c in t.deck
    }
    all i: Int | {
        no t.players[i]
    }
    no t.table
    some t.deck

    t.playing = 1
}

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
    -- If a card is gone from the deck, it must be in the player who played in the prev turn
    all c: Card | (c in prev.deck and not c in post.deck) implies {
        c in post.table or c in post.players[prev.playing]
    }

    -- Frame
    staysSameIfNotPrevPlaying[prev, post]
}

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