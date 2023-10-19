# Proofmood

Proofmood is a computer logic system specifically tailored for Fitch calculus, covering propositional logic, first-order logic, and type theory. It comprises a Fitch-style proof editor, verifier, and an automated proof generator.

Distinguishing itself from other computer logic systems, Proofmood emphasizes _human readability_ in the proofs it produces. The primary objective of this project is to furnish mathematicians and students with a pragmatic tool for crafting mathematical proofs.

The genesis of this project traces back to 2009. Currently, Proofmood can be accessed at https://proofmood.mindconnect.cc, and the website operates on the LAMP (Linux, Apache, MySQL, PHP) stack. It currently lacks an automatic proof generator, with implementations limited to propositional logic and first-order logic. Notably, type theory has not been incorporated, and it's essential to mention that the user interface is exclusively in Korean.

The core logic engine powering Proofmood was developed using JavaScript. As of May 2023, a decision has been made to transition to Python and initiate a comprehensive rewrite of the logic engine using Python. This repository offers Jupyter notebooks as the interface to Python modules, providing the flexibility to experiment freely by modifying the `.ipynb` files.

There are plans to convert the aforementioned website, https://proofmood.mindconnect.cc, from the LAMP stack to a Django/Vue stack in the future.

To comprehend the contents of this repository, it would be beneficial to have a fundamental understanding of Python, Jupyter Notebook, and mathematical logic.

You can contact me at jhjeong314@gmail.com and/or treenote@snu.ac.kr.

---

## 0. Readme

1. Most `.ipynb` files in this repo are also uploaded to Google Colab, allowing you to run the code in your web browser. Please take note that Google Colab may not function optimally on mobile devices at times. We recommend using a desktop web browser for the best experience.
1. The contents of the `Document.pdf` provide an explanation of the fundamental theories that underlie this repository, as well as its actual implementation.

## 1. Arithmetic expressions

Before we start working on logical formulas, we prepare some tools for parsing and displaying the AST(abstract syntax tree) of arithmetic expressions in various formats such as Polish notation, RPN, infix notation with $\LaTeX$ enabled, and bussproof style tree. [[Go to Arithmetic expressions](https://github.com/jhjeong314/Proofmood/blob/main/1arithmetic_expressions.md)]

## 2. Logical formulas

1. Parser for Propositional Formulas (`propositional_logic_parser.ipynb`)  
  [GitHub](./logical_formulas/propositional_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1G4jS1WhPSuLveu1V8ga5j857Bz9-9ZZY?usp=sharing)
1. Parser for First-order Formulas (`first_order_logic_parser.ipynb`)  
  [GitHub](./logical_formulas/first_order_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/17xmiho3-Hf0bveFaIIvTe2Dr_8VC2V93?usp=sharing)

Added a new showOption called `bussproof`. This option does not generate a diagram but instead produces LaTeX code that can be seamlessly incorporated into a LaTeX document. 
To ensure correct compilation of the source `.tex` file, it is necessary to include the `\usepackage{bussproofs}` command in the preamble.


## 3. Fitch Proof Verifier

Henceforth, both Text mode and LaTeX mode are available.  The latter prints out the LaTeX source code that can be compiled with the aid of `\usepackage{proofmood}`.  Truth table doesn't need this package.

1. Truth Table (`truth_table.ipynb`)  
[GitHub](./logical_formulas/truth_table.ipynb) | [Google Colab](https://colab.research.google.com/drive/1_CK9IwWhMy4DkOSCYxjeD5YkQyaiQyaw?usp=sharing)
1. Propositional Logic (`validate_proof.ipynb`) Fitch proof editor and verifier for propositional logic.  
[GitHub](./proofs_propositional/validate_proof.ipynb) | [Google Colab](https://colab.research.google.com/drive/1RjmIWlpfpVbrR4ijKEqMdlhSs5q3shBU?usp=sharing)
1. Tautologies (`tautologies.ipynb`) Fitch proofs for some important tautologies.  
[GitHub](./proofs_propositional/tautologies.ipynb) | [Google Colab](https://colab.research.google.com/drive/1k4-uz5QScpRPnUW0GE8-kztemDTNh47M?usp=sharing)

## 4. Fitch Proof Generator

1. Alpha-beta pruning  
[GitHub](https://github.com/jhjeong314/CS_Math) | [Google Colab](https://colab.research.google.com/drive/1QBi6fV4Pq3wA9A7JKGV-WFBGeKWZVgeD?usp=sharing)   
Not used for the time being.  Nevertheless this is included here because I believe that this tree searching algorithm will be used later for Fitch proof trees.  

1. Automatic annotation: This represents the initial phase of automatic Fitch proof generation. (`search_ann.ipynb`) [GitHub](./proofs_propositional/search_ann.ipynb)
    - When supplied with a proof text, it accurately annotates any lines that lack proper annotations within the conclusion formulas, assuming the requisite formulas or subproofs already exist.
    - Hypotheses, comments, and blank lines remain unaltered.
    - This process does not involve the creation or deletion of formulas or subproofs.

1. Automatic annotation examples
    - (`search_ann_ex0.ipynb`) [GitHub](./proofs_propositional/search_ann_ex0.ipynb)
    - (`search_ann_ex1.ipynb`) [GitHub](./proofs_propositional/search_ann_ex1.ipynb)