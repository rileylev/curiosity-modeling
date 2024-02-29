#lang forge

open "cm.sh.frg"
open "cm.sigs.frg"
open "cm.cards.frg"
open "cm.score.frg"

fun countSuit[s: Suit]: Int {
    #{c: Card | c.suit = s}
}

pred fiveBright { countSuit[Bright] = 5 }
pred sevenAnimal { countSuit[Animal] = 7 }
pred nineRibbon { countSuit[Ribbon] = 9 }
pred twentyThreeJunk { add[countSuit[Junk1], countSuit[Junk2]] = 23 }
pred fourDoubleJunk { countSuit[DoubleJunk] = 4 }

pred fourtyEightCards {
    #{c: Card | true} = 48
}

test suite for cardWellformed {
    -- We enforce an exactly 48 card constraint afterwards for optimization, but
    -- we want to make sure that even without this constraint, we would still have
    -- 48 cards
    assert cardWellformed is sufficient for fourtyEightCards for 7 Int
    assert cardWellformed is sufficient for fiveBright for exactly 48 Card, 7 Int
    assert cardWellformed is sufficient for sevenAnimal for exactly 48 Card, 7 Int
    assert cardWellformed is sufficient for nineRibbon for exactly 48 Card, 7 Int
    assert cardWellformed is sufficient for twentyThreeJunk for exactly 48 Card, 7 Int
    assert cardWellformed is sufficient for fourDoubleJunk for exactly 48 Card, 7 Int
}

test suite for winning {
    assert all t: Turn | winning[t] is necessary for winning[Game.next[t]] for exactly 48 Card, 7 Int
}

