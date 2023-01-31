# MIE396-Project2
Propositional Logic Reasoning for the Knights and Knaves Puzzles


## Background
[Knights and Knaves](https://en.wikipedia.org/wiki/Knights_and_Knaves) is a set of logical puzzles first introduced by the logician and mathematician Raymond Smullyan in 1978.

The puzzles are set on a fictional island where all inhabitants are either knights, who always tell the truth, or knaves, who always lie. The puzzles involve a visitor to the island who meets small groups of inhabitants. In this project, you are the visitor with the goal of deducing the inhabitants' type from their statements. This requires quite some intelligence, right? No worries! You have an AI running a DPLL algorithm to help you. 
More specifically, your task is to properly encode the conversations between you and the inhabitants using propositional logic, build a knowledge base, and reason over the knowledge base, so as to tell who are knights and who are knaves.

Please answer directly in this file and complete **data/knights.txt**. You are allowed to insert hand-written answers as figures in this file, while you should guarantee they are clearly readable.

## Q1 (1.5 Marks) Understanding the Problem
Each inhabitant is either a knight or a knave. A knight will always tell the truth: if a knight states a sentence, then that sentence is true. Conversely, a knave will always lie: if a knave states a sentence, then that sentence is false. Suppose you encounter two inhabitants *A* and *B*. *A* told you that *B* is a knight, and *B* said that himself and *A* are different. 

**Q1.1 (0.2 Marks)** Define a new propositional variables to represent *A* is a knight, *A* is a knave, *B* is a knight, and *B* is a knave.

*Please answer here*

**Q1.2 (0.3 Marks)** Represent *A and B are different* using propositional logic. Your answer should be in Conjunctive Normal Form (CNF).

*Please answer here*

**Q1.3 (1 Marks)** *A* is a knight or a knave? What about *B*? Use a truth table to solve the puzzle with explanations. 

*Please answer here*



## Further Notes
* You can browse more Knights and Knaves puzzles [here](https://philosophy.hku.hk/think/logic/knights.php).
* This project has no competitive components.
* The reasoner is based on the Scott Sanner's [implementation](link?)

