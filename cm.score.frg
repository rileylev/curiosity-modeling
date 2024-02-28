#lang forge

open "cm.sigs.frg"

pred redPoetryMatchingRibbon[p: Player] {
  #{c: Card | c in p.hand and c.suit = Ribbon and 
  c.month = Jan or c.month = Feb or c.month = Mar} = 3
}

pred redMatchingRibbon[p: Player] {
  #{c: Card | c in p.hand and c.suit = Ribbon and 
  c.month = Apr or c.month = May or c.month = Jul} = 3
}

pred blueMatchingRibbon[p: Player] {
  #{c: Card | c in p.hand and c.suit = Ribbon and 
  (c.month = Jun or c.month = Sep or c.month = Oct)} = 3
}

pred godori[p: Player] {
  #{c: Card | c in p.hand and c.suit = Animal and 
  (c.month = Feb or c.month = Apr or c.month = Aug)} = 3
}

fun countSuitInHand[p: Player, s: Suit]: Int {
    #{c: Card | c in p.hand and c.suit = s}
}

fun countJunkInHand[p: Player]: Int {
    add[countSuitInHand[p, Junk], multiply[countSuitInHand[p, DoubleJunk], 2]]
}

-- simplified scoring logic. No special case scoring
fun score[p: Player]: Int {
    sum[
        (countSuitInHand[p, Bright] >= 3 =>
        countSuitInHand[p, Bright] else 0),

        (countSuitInHand[p, Ribbon] >= 5 =>
        subtract[countSuitInHand[p, Ribbon], 4] else 0),

        (countSuitInHand[p, Animal] >= 5 =>
        subtract[countSuitInHand[p, Animal], 4] else 0),

        (countJunkInHand[p] >= 10 =>
        subtract[countJunkInHand[p], 9] else 0)
    ]
}

pred winning {
  some p: Player | {
    score[p] >= 3
  }
}

