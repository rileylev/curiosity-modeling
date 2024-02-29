#lang forge

open "gostop.frg"
open "sigs.frg"
open "score.frg"

pred playerHasThreeBright[t: Turn] {
    some i: Int | {
        #{c: Card | c in t.players[i] and c.suit = Bright} = 3
    }
}
pred playerHasFiveRibbon[t: Turn] {
    some i: Int | {
        #{c: Card | c in t.players[i] and c.suit = Ribbon} = 5
    }
}
pred playerHasFiveAnimal[t: Turn] {
    some i: Int | {
        #{c: Card | c in t.players[i] and c.suit = Animal} = 5
    }
}
pred playerHasTenJunk[t: Turn] {
    some i: Int | {
        add[
            #{c: Card | c in t.players[i] and c.suit = Junk1}, 
            #{c: Card | c in t.players[i] and c.suit = Junk1}, 
            multiply[#{c: Card | c in t.players[i] and c.suit = DoubleJunk}, 2]
        ] = 10
    }
}

test suite for winning {
    // assert all t: Turn | winning[t] is necessary for winning[Game.next[t]] for exactly 48 Card, 7 Int
    assert all t: Turn | playerHasThreeBright[t] is sufficient for winning[t] for exactly 48 Card, 7 Int
    assert all t: Turn | playerHasFiveRibbon[t] is sufficient for winning[t] for exactly 48 Card, 7 Int
    assert all t: Turn | playerHasFiveAnimal[t] is sufficient for winning[t] for exactly 48 Card, 7 Int
}