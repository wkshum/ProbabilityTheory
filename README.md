This repo is an AI-assisted Lean 4 formalization of my book _Measure-Theoretic Probability: With Applications to Statistics, Finance, and Engineering_  (Birkhauser, Compact Textbooks in Mathematics, [Publisher's webpage](https://link.springer.com/book/10.1007/978-3-031-49830-5)). This is a textbook for a second course in probability theory.
  
---
### Contributors 

This formalization project was developed by **Shuo Deng**, with assistance from ChatGPT and the ToyApollo project.

---

### Lean version
The Lean programs depend on Mathlib, version 4.31

`leanprover/lean4:v4.31.0`

---

### Number of definitions and theorems formulated

We formulate all definitions and verify all theorems in the book. Most of the examples and exercises are included.

| Type       | Count |
| ---------- | ----- |
| Definition | 81    |
| Theorem    | 127   |
| Example    | 107   |
| Problem    | 134   |
#### Naming convention

- `def_C_N` / `thm_C_N` / `ex_C_S_N` / `prob_C_N` -- definition / theorem / example / problem, where `C` is the chapter, `S` is the section, and `N` is a number.  For example, `def_2_1` is Definition 2.1 in the textbook.

- A module name `thm_9_5_2` with an extra numeric suffix is a helper lemma for the parent task (`thm_9_5`). 

---
### How to compile?

All theorems are in the subdirectory `ProbabilityTheory`, organized according to chapters. Clone the folder `ProbabilityTheory`, and add the lines 

`[[lean_lib]]`
`name = "ProbabilityTheory"`

in the file `lakefile.toml`, so that the Lean programs can import files in the same folder. All relevant theorems and programs are listed in `Main.lean`.

---

### Connection to Mathlib and logical dependency

Mathlib already contains a lot of theorems on measure theory. Since Mathlib aims as the highest level of abstraction, many definitions from the book are not the same as the corresponding ones in Mathlib. Some modules are specifically constructed to bridge the gap.

Some examples and definitions in Chapter 1 require the notion of measurable sets and measure, which are defined in Chapters 2 and 3.

A **bridge** is a module that translates between three vocabularies: the textbook's conventions, the project's local definitions, and Mathlib's APIs. 

For examples: 
- `rs_stieltjes_measure_bridge` (Riemann–Stieltjes interface), 
- `gamma_beta_bridge`, 
- `dirichlet_simplex_bridge`. 
A bridge is an interface, not a workaround for a single proof. 

The project distinguishes four layers of functionality:
- _task parent_ -- the module formulating the statement for an item in the book
- _proof-layer support_ -- large single-purpose proof machinery owned by one task, 
- _interface support_ -- the same as bridges as above, and 
- _shared support_ -- module that supports several tasks, e.g. `Support.IIDWord`. 

--- 

### Content


| Chapter 1 | Beyond Discrete and Continuous Random Variables  |                                                                                    |
| --------- | ------------------------------------------------ | ---------------------------------------------------------------------------------- |
| Section 1 | Discrete and continuous random variables         | not formalized                                                                     |
| Section 2 | Random variables of mixed type and singular type | Def 1.1, Ex. 1.2.1, Ex 1.2.2, Ex 1.2.3.                                            |
| Section 3 | Riemann-Stieltjes integrals                      | Def 1.2, Def 1.3, Def 1.4, Thm 1.1, Thm 1.2, Thm 1.3, Thm 1.4, Ex 1.3.1, Ex. 1.3.2 |
| Section 4 | Problems                                         | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10                                            |


| Chapter 2 | Probability Spaces |                                                                          |
| --------- | ------------------ | ------------------------------------------------------------------------ |
| Section 1 | Countable sets     | Def 2.1, Ex 2.1.1, Ex 2.1.2                                              |
| Section 2 | Algebra of events  | Def 2.2, Def 2.3, Def 2.4, Thm 2.1, Ex 2.2.1,  Ex 2.2.2,                 |
| Section 3 | Measure functions  | Def 2.5, Def 2.6, Thm 2.2, Thm 2.3, Thm 2.4, Thm 2.5, Ex 2.3.1, Ex 2.3.2 |
| Section 4 | Borel sets         | Def. 2.7, Def 2.8, Thm 2.6, Thm 2.7, Thm 2.8, Ex 2.4.1                   |
| Section 5 | Vitali set         | Thm 2.9                                                                  |
| Section 6 | Problems           | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12                        |


| Chapter 3 | Lebesgue-Stieltjes Measures     |                                                                                                         |
| --------- | ------------------------------- | ------------------------------------------------------------------------------------------------------- |
| Section 1 | Pre-measure                     | Def 3.1, Def 3.2, Def 3.3, Thm 3.1, Ex 3.1.1, Ex. 3.1.2, Ex 3.1.3, Ex 3.1.4                             |
| Section 2 | Stieltjes measure function      | Def 3.4, Def 3.5, Thm 3.2, Ex 3.2.1                                                                     |
| Section 3 | Lebesgue-Stieltjes measures     | Def 3.6, Def 3.7, Def 3.8, Thm 3.4, Thm 3.5, Ex 3.3.1, Ex 3.3.2, Ex 3.3.3, Ex 3.3.4, Ex 3.3.5, Ex 3.3.6 |
| Section 4 | Null sets and complete measures | Def 3.9, Thm 3.6                                                                                        |
| Section 5 | Uniqueness of measure extension | Def 3.10, Thm 3.7, Thm 3.8, Thm 3.9                                                                     |
| Section 6 | Problems                        | P1, P2, P3, P4, P5, P6, P7, P8, P9                                                                      |


| Chapter 4 | Measurable Functions and Random Variables |                                                                                |
| --------- | ----------------------------------------- | ------------------------------------------------------------------------------ |
| Section 1 | Measurable functions                      | Def 4.1, Def 4.2, Thm 4.1, Ex 4.1.1, Ex 4.1.2                                  |
| Section 2 | Composition of measurable functions       | Thm 4.2, Thm 4.3, Thm 4.4, Thm 4.5                                             |
| Section 3 | Operations with measurable functions      | Thm 4.6, Thm 4.7, Thm 4.8, Ex 4.3.1, Ex 4.3.2, Definition of limsup and liminf |
| Section 4 | Complex-valued random variables           | Complex number, complex random variables, Ex 4.4.1, Ex 4.4.2, Ex 4.4.3         |
| Section 5 | Problems                                  | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12, P13                         |


| Chapter 5 | Statistical Independence                                         |                                                                                   |
| --------- | ---------------------------------------------------------------- | --------------------------------------------------------------------------------- |
| Section 1 | Independence of two random variables                             | Def 5.1, Def 5.2, Def 5.3, Def 5.4, Thm 5.1, Thm 5.2, Ex 5.1.1                    |
| Section 2 | Independent random variables of discrete type or continuous type | Thm 3, Thm 4, Thm 5.5, Ex 5.2.1, Ex 5.2.2                                         |
| Section 3 | Independence of more than two random variables                   | Def 5.5, Def 5.6, Def 5.7, Def 5.8, Def 5.9, Def 5.10, Thm 5.6, Thm 5.7, Ex 5.3.1 |
| Section 4 | Borel-Cantelli lemmas                                            | Ex 5.4.1, Ex 5.4.2, Ex 5.4.3, Thm 5.8, Thm 5.9, Thm 5.10, Thm 5.11                |
| Section 5 | A model for a sequence of independent random variables           | not formalized                                                                    |
| Section 6 | Problems                                                         | P1, P2, P3, P4, P5, P6, P7, P8, P9                                                |


| Chapter 6 | Lebesgue Integral and Mathematical Expectation                |                                                                  |
| --------- | ------------------------------------------------------------- | ---------------------------------------------------------------- |
| Section 1 | Simple functions                                              | Def 6.1, Def 6.2, Thm 6.1, Thm 6.2, Ex 6.1.1, Ex 6.1.2           |
| Section 2 | Lebesgue integral of nonnegative functions                    | Def 6.3, Thm 6.3, Thm 6.4, Thm 6.5                               |
| Section 3 | Lebesgue integral of real-valued and complex-valued functions | Def 6.4, Def 6.5, Def 6.6, Thm 6.6, Thm 6.7,  Ex 6.3.1, Ex 6.3.2 |
| Section 4 | Mathematical expectation of random variables                  | Def 6.7, Ex 6.4.1, Ex 6.4.2                                      |
| Section 5 | Application: Hat problem and ball-and-bin model               | Ex 6.5.1, Ex 6.5.2                                               |
| Section 6 | Problems                                                      | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10                          |


| Chapter 7 | Properties of Lebesgue Integral and Convergence Theorem        |                                                                           |
| --------- | -------------------------------------------------------------- | ------------------------------------------------------------------------- |
| Section 1 | Almost-everywhere equality                                     | Def 7.1, Thm 7.1, Thm 7.2                                                 |
| Section 2 | Fatou's lemma and dominated convergence theorem                | Thm 7.3, Thm 7.4, Thm 7.5, Thm 7.6, Thm 7.7, Ex 7.2.1, Ex 7.2.2, Ex 7.2.3 |
| Section 3 | Application: Evaluation of Lebesgue-Stieltjes integrals        | Thm 7.8, Thm 7.9, Ex 7.3.1, Ex 7.3.2                                      |
| Section 4 | Push-forward measure and change-of-variable formula            | Def 7.2, Thm 7.10, Thm 7.11, Thm 7.12, Ex 7.4.1, Ex 7.4.2                 |
| Section 5 | Expectation of the product of two independent random variables | Def 7.3, Thm 7.13, Ex 7.5.1                                               |
| Section 6 | Problems                                                       | P1, P2, P3, P4, P5, P6, P7, P8, P9                                        |


| Chapter 8 | Product Space and Coupling                         |                                                                           |
| --------- | -------------------------------------------------- | ------------------------------------------------------------------------- |
| Section 1 | Coupling                                           | Def 8.1, Def 8.2, Def 8.3, Def 8.4, Thm 8.1, Ex 8.1.1, Ex 8.1.2, Ex 8.1.3 |
| Section 2 | Product measure and Fubini theorem                 | Thm 8.2, Thm 8.3, Thm 8.4, Thm 8.5, Ex 8.2.1, Ex 8.2.2                    |
| Section 3 | Application: Monge problem and Kantorovich problem | Ex 8.3.1, Ex 8.3.3, Ex 8.3.4                                              |
| Section 4 | Application: Total variation distance              | Def 8.4, Ex 8.4.1, Ex 8.4.2, Ex 8.4.3, Ex 8.4.4, Thm 8.6, Thm 8.7         |
| Section 5 | Problems                                           | P1, P2, P3, P4, P5, P6, P7                                                |


| Chapter 9 | Moment Generating Functions and Characteristic Functions |                                                                          |
| --------- | -------------------------------------------------------- | ------------------------------------------------------------------------ |
| Section 1 | Moments and moment generating functions                  | Def 9.1, Def 9.2, Thm 9.1, Thm 9.2, Ex 9.1.1                             |
| Section 2 | Characteristic functions                                 | Def 9.3, Thm 9.3, Thm 9.4, Thm 9.5, Thm 9.6, Thm 9.7, Ex 9.2.1, Ex 9.2.2 |
| Section 3 | Problems                                                 | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11                             |


| Chapter 10 | Modes of Convergence                                     |                                                                                   |
| ---------- | -------------------------------------------------------- | --------------------------------------------------------------------------------- |
| Section 1  | Convergence almost surely and convergence in probability | Def 10.1, Def 10.2, Thm 10.1, Thm 10.2, Thm 10.3 Thm 10.4, Ex 10.1.1              |
| Section 2  | Convergence in the mean                                  | Def 10.3, Thm 10.5, Ex 10.2.1, Ex 10.2.2                                          |
| Section 3  | Convergence in distribution and in total variation       | Def 10.4, Def 10.5, Thm 10.6, Thm 10.7, Thm 10.8, Ex 10.3.1, Ex 10.3.2, Ex 10.3.3 |
| Section 4  | Convergence of random vectors                            | Def 10.6, Thm 10.9, Thm 10.10                                                     |
| Section 5  | Application: Continuous mapping theorem                  | Thm 10.11, Thm 10.12, Ex 10.5.1                                                   |
| Section 6  | Problems                                                 | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10                                           |

| Chapter 11 | Laws of Large Numbers                |                                          |
| ---------- | ------------------------------------ | ---------------------------------------- |
| Section 1  | Some useful bounds and inequalities  | Thm 11.1, Thm 11.2, Thm 11.3             |
| Section 2  | Weak law of large numbers            | Thm 11.4, Thm 11.5, Thm 11.6             |
| Section 3  | Application: Monte Carlo integration | not formalized                           |
| Section 4  | Application: Data compression        | not formalized                           |
| Section 5  | Strong law of large numbers          | Thm 11.7, Thm 11.8, Ex 11.5.1, Ex 11.5.2 |
| Section 6  | Problems                             | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10  |

| Chapter 12 | Techniques from Hilbert Space Theory |                                                                                  |
| ---------- | ------------------------------------ | -------------------------------------------------------------------------------- |
| Section 1  | L2-norm and inner product space      | Def 12.1, Def 12.2, Def 12.3, Thm 12.1, Thm 12.2, Thm 12.3, Ex 12.1.1, Ex 12.1.2 |
| Section 2  | Closed subspace and projection       | Def 12.4, Def 12.5, Thm 12.4, Ex 12.2.1, Ex 12.2.2, Ex 12.2.3                    |
| Section 3  | Orthogonality principle              | Thm 12.5, Thm 12.6, Ex 12.4.1, Ex 12.4.2, Ex 12.4.3                              |
| Section 4  | Application. MMSE estimation         | Ex 12.4.1, Ex 12.4.2, Ex 12.4.3                                                  |
| Section 5  | Problems                             | P1, P2, P3, P4, P5                                                               |

| Chapter 13 | Conditional Expectations                                    |                                                                                                                                           |
| ---------- | ----------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------- |
| Section 1  | Expectation conditioned on a finite partition               | Def 13.1, Def 13.2, Thm 13.1, Thm 13.2                                                                                                    |
| Section 2  | Expectation conditioned on  a sub-sigma-algebra             | Def 13.3, Def 13.4, Def 13.5, Thm 13.3, Thm 13.4, Ex 13.2.1, Ex 13.2.2                                                                    |
| Section 3  | Properties of conditional expectation                       | Thm 13.5, Thm 13.6, Thm 13.7, THm 13.8, Thm 13.9, Thm 13.10,  Ex 13.3.1                                                                   |
| Section 4  | Conditional expectation given a discrete random variables   | Thm 13.11, Thm 13.12, Thm 13.13                                                                                                           |
| Section 5  | Conditional expectation given a continuous random variables | Thm 13.14, Ex 13.5.1                                                                                                                      |
| Section 6  | Application: Martingale and stopping time                   | Def 13.6, Def 13.7, Def 13.8, Def 13.9, Thm 13.15, Thm 13.16, Thm 13.17, Thm 13.18, Ex 13.6.1, Ex 13.6.2, Ex 13.6.3, Ex 13.6.4, Ex 13.6.5 |

| Chapter 14 | Levy's Continuity Theorem and Central Limit Theorem |                                                            |
| ---------- | --------------------------------------------------- | ---------------------------------------------------------- |
| Section 1  | Weak convergence                                    | Def 14.1, Def 14.2, Thm 14.1, Thm 14.2, Thm 14.3, Thm 14.4 |
| Section 2  | Tightness of a sequence of measures                 | Def 14.3, Thm 14.5, Ex 14.2.1                              |
| Section 3  | Prokhorov theorem and sequential compactness        | Thm 14.6, Ex 14.3.1, Ex 14.3.2                             |
| Section 4  | Central limit theorems                              | Thm 14.7, Thm 14.8, Ex 14.4.1, Ex 14.4.2, Ex 14.4.3        |
| Section 5  | Problems                                            | P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, P12          |

