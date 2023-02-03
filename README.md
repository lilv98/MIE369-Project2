# MIE369-Project2
Propositional Logic Reasoning for the Knights and Knaves Puzzles


## Background
[Knights and Knaves](https://en.wikipedia.org/wiki/Knights_and_Knaves) is a set of logical puzzles first introduced by the logician and mathematician Raymond Smullyan in 1978.

The puzzles are set on a fictional island where all inhabitants are either knights, who always tell the truth, or knaves, who always lie. The puzzles involve a visitor to the island who meets small groups of inhabitants. In this project, you are the visitor with the goal of deducing the inhabitants' type from their statements. This requires quite some intelligence, right? No worries! You have an AI running a DPLL algorithm to help you. More specifically, your task is to properly encode the inhabitants' statements using propositional logic, build a knowledge base, and reason over the knowledge base, so as to tell who are knights and who are knaves.

Please answer directly in this file and complete the files in **data**. You are allowed to insert hand-written answers as figures in this file, while you should guarantee they are clearly readable.

## Q1 (1.5 Marks) Understanding the Problem
Each inhabitant is either a knight or a knave. A knight will always tell the truth: if a knight states a sentence, then that sentence is true. Conversely, a knave will always lie: if a knave states a sentence, then that sentence is false. Suppose you encounter two inhabitants *A* and *B*. *A* told you that *B* is a knight, and *B* said that himself and *A* are different. 

**Q1.1 (0.2 Marks)** Define a new propositional variables to represent *A* is a knight, *A* is a knave, *B* is a knight, and *B* is a knave.

*Please answer here*

**Q1.2 (0.3 Marks)** Represent *A and B are different* using propositional logic. Your answer should be in Conjunctive Normal Form (CNF).

*Please answer here*

**Q1.3 (1 Marks)** *A* is a knight or a knave? What about *B*? Use a truth table to solve the puzzle with explanations. 

*Please answer here*

## Q2 (1.5 Marks) The DPLL Reasoner
Although we can always use the truth table to identify knights and knaves, sometimes the problem will getting more tricky such that you may need assistance from an AI. We provide a DPLL reasoner to help you. Please refer to the following table for the basic format of the input propositions.

| Symbol | Meaning |
| ------ |:-------:|
| ~      | not     |
| ^      | and     |
| &#124; | or      |
| =>     | implication      |
| <=> | biconditional (equivalence) |

Here is an example proposition: a => ( ( b <=> ( c | d ) ) ^ e ). You can use

    tell "your propositional knowledge"
to add knowledge to your AI, and use

    ask "your propositional query"
to ask your AI to reason based on the knowledge and the query. 

**Q2.1 (0.5 Marks)** Have a look at the propositions in **./data/example.txt**, explain line 17 and 19.

*Please answer in* **./data/example.txt**

**Q2.2 (0.5 Marks)** Run the DPLL reasoner using:

    java -cp bin ./code/logic/PropAskTell.java ./data/example.txt
or simply run **./code/logic/PropAskTell.java** with your prefered IDE (recommended) and pass **./data/example.txt** as the argument.
Report the output of the queries in **./data/example.txt**. Are the results as expected? Explain each of them.

*Please answer in* **./data/example.txt**

**Q2.3 (0.5 Marks)** Can we tell Joe is clever or not using the existing queries? Why or why not? If not, design the query and report the output.

*Please answer here*

## Q3 (7 Marks) 
**data/knights.txt**


## Further Notes
* You can browse more Knights and Knaves puzzles [here](https://philosophy.hku.hk/think/logic/knights.php).
* This project has no competitive components.
* The reasoner is based on the Scott Sanner's implementation.

