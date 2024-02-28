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

-- Represents the START of a turn
sig Turn {
    players: set Int -> Card,
    table: set Card,
    deck: set Card,
    -- the player who WILL go
    playing: one Int
}

one sig Game {
    firstTurn: one Turn,
    next: pfunc Turn -> Turn
}

sig CardSetWrapper {
  cardset: set Card
}
