# Go-Stop
[Go-Stop](https://en.wikipedia.org/wiki/Go-Stop) is a Korean card game played with Hanafuda (or _Hwatu_ as they are known in Korean) cards. Hwatu cards have a Suit (Bright, Animal, Ribbon, Junk/Double Junk) and a Month (Jan-Dec). The cards are not necessarily unique. The gameplay involves drawing cards from the deck and matching cards by Suit from the player's hand and the table. It is generally played with 2-3 players, and we model the three player version.

Even though our model simplifies Go-Stop, it uses the full set of cards as real Go-Stop and preserves the core gameplay loop: that is, our model goes through each step taken in a real Go-Stop game. We merely cut out special cases for scoring which are added on top of the base rule such as Godori scoring. If you are interested in what some of these special rules look like, the `extensions.frg` file has some instances of special rules we wrote, but never quite got to integrating into our model.

