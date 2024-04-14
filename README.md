# solc-lean4

This is a (very) experimental, and only partially completed shallow embedding of the [proposed new
typechecker](https://notes.ethereum.org/mJh3mh3jS6euVl_NBDYBUg) for solidity into lean4.

Core solidity blocks currently do not have any custom syntax expansion, and are implemented by
simply writing the restricted subset of monadic lean code that matches the proposal. Custom syntax
for Yul is implemented and `assembly {}` blocks are macro expanded into monadic lean4 code.
