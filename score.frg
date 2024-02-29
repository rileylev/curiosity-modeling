#lang forge

open "sigs.frg"

fun countSuitInHand[hand: set Card, s: Suit]: Int {
    #{c: Card | c in hand and c.suit = s}
}

fun countJunkInHand[hand: set Card]: Int {
    add[countSuitInHand[hand, Junk1], countSuitInHand[hand, Junk2], multiply[countSuitInHand[hand, DoubleJunk], 2]]
}

-- simplified scoring logic. No special case scoring
fun score[hand: set Card]: Int {
    add[
        (countSuitInHand[hand, Bright] >= 3 =>
        countSuitInHand[hand, Bright] else 0),

        (countSuitInHand[hand, Ribbon] >= 5 =>
        subtract[countSuitInHand[hand, Ribbon], 4] else 0),

        (countSuitInHand[hand, Animal] >= 5 =>
        subtract[countSuitInHand[hand, Animal], 4] else 0),

        (countJunkInHand[hand] >= 10 =>
        subtract[countJunkInHand[hand], 9] else 0)
    ]
}

pred winning[t: Turn] {
  some i: Int | {
    score[t.players[i]] >= 3
  }
}