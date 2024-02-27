#lang forge

// at its most abstract, a card is just a tuple
sig Suite { }
sig Month { }

sig Card {
  suite: Suite
  month: Month
}

sig Hand {
  holds: set Card
}

sig Node {}
sig Nil extends Node {}
sig Cons {
  head: Card
  tail: Node
}

sig Deck {
  top: Node
}
