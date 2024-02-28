#lang forge

open "cm.frg"

pred countSuit[s: Suit, n: Int] {
    #{c: Card | c.suit = s} = n
}


test suite for cardWellformed {
    assert cardWellformed is sufficient for countSuit[Bright, 5] for 48 Card
    assert cardWellformed is sufficient for countSuit[Animal, 7] for 48 Card
    assert cardWellformed is sufficient for countSuit[Ribbon, 9] for 48 Card
    assert cardWellformed is sufficient for countSuit[Junk, 23] for 48 Card
    assert cardWellformed is sufficient for countSuit[DoubleJunk, 4] for 48 Card
}

