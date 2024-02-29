#lang forge

open "sigs.frg"

pred twoJunkForMonth[m: Month] {
  one card: Card | card.month = m implies {
    card.suit = Junk1
  }
  one card: Card | card.month = m implies {
    card.suit = Junk2
  }
}

pred twoJunkUnlessDec {
  twoJunkForMonth[Jan]
  twoJunkForMonth[Feb]
  twoJunkForMonth[Mar]
  twoJunkForMonth[Apr]
  twoJunkForMonth[May]
  twoJunkForMonth[Jun]
  twoJunkForMonth[Jul]
  twoJunkForMonth[Sep]
  twoJunkForMonth[Oct]
  twoJunkForMonth[Nov]
}

// pred oneEachForNonJunk[m: Month] {
//   #{card: Card | card.month = m and card.suit = Bright} < 2
//   #{card: Card | card.month = m and card.suit = Animal} < 2
//   #{card: Card | card.month = m and card.suit = Ribbon} < 2
//   #{card: Card | card.month = m and card.suit = DoubleJunk} < 2
// }

// pred oneEachForNonJunkAll {
//   oneEachForNonJunk[Jan]
//   oneEachForNonJunk[Feb]
//   oneEachForNonJunk[Mar]
//   oneEachForNonJunk[Apr]
//   oneEachForNonJunk[May]
//   oneEachForNonJunk[Jun]
//   oneEachForNonJunk[Jul]
//   oneEachForNonJunk[Sep]
//   oneEachForNonJunk[Oct]
//   oneEachForNonJunk[Nov]
// }

pred fourOfEachSuite {
  #{card: Card | card.month = Jan} = 4
  #{card: Card | card.month = Feb} = 4
  #{card: Card | card.month = Mar} = 4
  #{card: Card | card.month = Apr} = 4
  #{card: Card | card.month = May} = 4
  #{card: Card | card.month = Jun} = 4
  #{card: Card | card.month = Jul} = 4
  #{card: Card | card.month = Aug} = 4
  #{card: Card | card.month = Sep} = 4
  #{card: Card | card.month = Oct} = 4
  #{card: Card | card.month = Nov} = 4
  #{card: Card | card.month = Dec} = 4
}

pred suitMonthCombo {
  all c: Card | {
    (c.month = Jan or c.month = Mar) 
    implies c.suit != Animal and c.suit != DoubleJunk
    
    (c.month = Feb or 
     c.month = Apr or
     c.month = Jun or
     c.month = Jul or
     c.month = Oct)
    implies c.suit != Bright and c.suit != DoubleJunk

    (c.month = May or c.month = Sep)
    implies c.suit != Bright and c.suit != Animal

    c.month = Aug implies c.suit != Ribbon and c.suit != DoubleJunk

    c.month = Nov implies c.suit != Animal and c.suit != Ribbon

    c.month = Dec implies c.suit != Ribbon
  }
}

pred cardWellformed {
  fourOfEachSuite
  twoJunkUnlessDec
  suitMonthCombo
}