#lang forge

open "sigs.frg"

pred allSuitMonthComboUnique {
  all disj a, b: Card | {
    a.month != b.month or a.suit != b.suit
  }
}

pred twoJunkForMonth[m: Month] {
  one card: Card | {
    card.month = m and card.suit = Junk1
  }
  one card: Card |  {
    card.month = m and card.suit = Junk2
  }
}

pred oneJunkForDec {
  one card: Card | {
    card.month = Dec and card.suit = Junk1
  }
  no card: Card | {
    card.month = Dec and card.suit = Junk2
  }
}

-- all months except december have two Junks
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
  oneJunkForDec
}

-- all months have four cards
pred fourOfEachMonth {
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

-- Outlines which months don't have which suites
pred monthNotHaveSuit {
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
  allSuitMonthComboUnique
  fourOfEachMonth
  twoJunkUnlessDec
  monthNotHaveSuit
}