#lang forge

// at its most abstract, a card is just a tuple
abstract sig Suit {}
abstract sig Month {}

one sig Bright, Animal, Ribbon, Junk, DoubleJunk extends Suit {}
one sig Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec extends Month {}


sig Card {
  suit: one Suit,
  month: one Month
}

sig Player {
  hand: set Card
}

one sig Deck {
  deck: set Card
}

one sig Table {
  table: set Card
}

pred allCardsInDeck {
  
}

pred initial {
  all c: Card | {
    c in Deck.deck
  }
  all p: Player | {
    no p.hand
  }
  no Table.table
}

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

pred threeOrMorePoints[p: Player] {
  #{c: Card | c in p.hand and c.suit = Bright} > 4 or
  #{c: Card | c in p.hand and c.suit = Bright and c.month != Dec} = 3 or
  #{c: Card | c in p.hand and c.suit = Ribbon} >= 7 or
  redPoetryMatchingRibbon
  redMatchingRibbon
  blueMatchingRibbon
  #{c: Card | c in p.hand and c.suit = Ribbon} >= 7 or
  #{c: Card | c in p.hand and c.suit = Junk} >= 10
}

pred winning {
  some p: Player | {

  }
}

// pred pop[pre, post: Deck, card: Card] {
//   card = pre.top.head
//   post.top = pre.top.tail
// }

pred twoJunkUnlessDec {
  #{card: Card | card.month = Jan and card.suit = Junk} = 2
  #{card: Card | card.month = Feb and card.suit = Junk} = 2
  #{card: Card | card.month = Mar and card.suit = Junk} = 2
  #{card: Card | card.month = Apr and card.suit = Junk} = 2
  #{card: Card | card.month = May and card.suit = Junk} = 2
  #{card: Card | card.month = Jun and card.suit = Junk} = 2
  #{card: Card | card.month = Jul and card.suit = Junk} = 2
  #{card: Card | card.month = Aug and card.suit = Junk} = 2
  #{card: Card | card.month = Sep and card.suit = Junk} = 2
  #{card: Card | card.month = Oct and card.suit = Junk} = 2
  #{card: Card | card.month = Nov and card.suit = Junk} = 2
}

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

sig Score { }

//I'm not sure how to do this
// sig State {
//   deck: Deck
//   hands: Player -> Hand
//   scores: Player -> Score
//   table: set Card
// }

run {
  cardWellformed
  initial
} for 48 Card

// Play begins with the dealer and continues counterclockwise.
// A turn begins with a player attempting to match one of the cards lying face-up on the table with a card of the same month in their hand. If there are two cards of the same month already on the table, the player may select one of them. If the player has no cards matching the cards on the table, the player discards a card to the table.
// The turn continues with the player flipping over the top card from the draw pile and looking for a card of the same month on the table. If the player finds a matching card on the table, the player collects both cards along with the cards matched in step 2. Otherwise, the drawn card is added to the table.
// If the card drawn from the top of the draw pile in step 3 matches the two cards matched in step 2, the three cards remain on the table. This is known as ppeok (뻑; ppeog). The three cards remain until a player collects them using the fourth card of the same month.
// If a player draws a card that matches the card discarded in step 2, the player collects both cards as well as one junk card (pi) from each opponent's stock pile. This is known as chok.
// If a player plays a card in step 2 for which two matching cards are already on the table, and then draws the fourth matching card from the draw pile in step 3, the player collects all four cards as well as one junk card (pi) from each opponent's stock pile. This is known as ttadak.[7]
// The object of the game is to create scoring combinations to accumulate points up to a score of either three (for three players) or seven (for two players), at which point a "Go" or a "Stop" must be called.
// A game that ends with neither a "Go" nor "Stop" call is called a Nagari game (나가리; nagali). The dealer and play order of the next game remain the same as with the Nagari game, and when the game ends, the loser owes the winner double money.
