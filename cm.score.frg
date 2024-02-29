#lang forge

open "cm.sigs.frg"

pred redPoetryMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  c.month = Jan or c.month = Feb or c.month = Mar} = 3
}

pred redMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  c.month = Apr or c.month = May or c.month = Jul} = 3
}

pred blueMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  (c.month = Jun or c.month = Sep or c.month = Oct)} = 3
}

pred godori[hand: set Card] {
  #{c: Card | c in hand and c.suit = Animal and 
  (c.month = Feb or c.month = Apr or c.month = Aug)} = 3
}

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