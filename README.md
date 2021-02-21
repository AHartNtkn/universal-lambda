# universal-lambda
An implementation of a universal function using the lambda calculus

This code demonstrates a universal function (a partial surjection over binary strings representing an evaluation of universal computation) using the lambda calculus as a basis. Unlike previous attempts at this (e.g. the binary lambda calculus), this uses bijections between lambda terms and ℕ on the input and bijections between normalized lambda terms and ℕ on the output so that any number/string can be treated as an input or an output. This means it's always meaningful to ask what the Kolmogorov complexity of a string is, for instance.

This will likely be absorbed into a larger project in the future. For the moment I decided to put it here.
