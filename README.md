# Proofmood


Proofmood is a computer logic system designed for Fitch calculus, encompassing propositional and first-order logic.

Presently, Proofmood is accessible at https://proofmood.mindconnect.cc, and the website operates on the LAMP (Linux, Apache, MySQL, PHP) stack. The logic engine behind Proofmood is implemented using JavaScript.

The inception of this project dates back to 2009. As of May 2023, I have made the decision to migrate to Django and completely rewrite the logic engine using Python.

To comprehend the contents of this repository, it would be beneficial to have a fundamental understanding of Python, Jupyter Notebook, and mathematical logic.

You can contact me at jhjeong314@gmail.com and/or treenote@snu.ac.kr.

---

## 0. Readme

1. Most `.ipynb` files in this repo are also uploaded to Google Colab, allowing you to run the code in your web browser. Please take note that Google Colab may not function optimally on mobile devices at times. We recommend using a desktop web browser for the best experience.
1. The contents of the `Document.pdf` provide an explanation of the fundamental theories that underlie this repository, as well as its actual implementation.

## 1. Arithmetic expressions

Before we start working on logical formulas, we prepare some tools for parsing and displaying the AST(abstract syntax tree) of arithmetic expressions in various formats such as Polish notation, RPN, infix notation with $\LaTeX$ enabled, and bussproof style tree.

1. LaTeX in Jupyter Notebook (`latex_in_jupyternotebook.ipynb`)  
  [GitHub](./tests/latex_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1JRn8m4_t77R-gJqjFSXiKaikWcDMQAnS?usp=sharing)
1. MathJax in Jupyter Notebook (`mathjax_in_jupyternotebook.ipynb`)  
  [GitHub](./tests/mathjax_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1rywvvBl6WIMHzCdW-HeH69kbf9XYjxCW?usp=sharing)
1. Parser for a simple arithmetic grammar (`arith4parser.ipynb`)  
  [GitHub](./attic/arith4parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1vpzjogSZi-QOx0QnBOxgPPFZkEJVKU1b?usp=sharing)
1. Parser for arithmetic. Added unary minus, postfix operators and exponentiation(right associative). (`arith5parser.ipynb`)  
  [GitHub](./attic/arith5parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/18niproAYizRP6BzWXYsCK6wGc0GJse1U?usp=sharing)
1. Parser for arithmetic. Added function symbols. Display expressions graphically using $\LaTeX$. (`arith6parser.ipynb`)  
  [GitHub](./attic/arith6parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1eAV9i2jEN39hfL7RbOsKnIW7qi-YveJa?usp=sharing)
1. Parsed expressions are now displayed as Bussproof style tree (`arith7parser.ipynb`)  
  [GitHub](./attic/arith7parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1Rv_vqzg8BtrmRfc16FwVsPYh3zNR07LE?usp=sharing)

## 2. Logical formulas

Added a new showOption called `bussproof`. This option does not generate a diagram but instead produces LaTeX code that can be seamlessly incorporated into a LaTeX document. 
To ensure correct compilation of the source .tex file, it is necessary to include the `\usepackage{bussproofs}` command in the preamble.

1. Parser for Propositional Formulas (`propositional_logic_parser.ipynb`)  
  [GitHub](./logical_formulas/propositional_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1G4jS1WhPSuLveu1V8ga5j857Bz9-9ZZY?usp=sharing)
1. Parser for First-order Formulas (`first_order_logic_parser.ipynb`)  
  [GitHub](./logical_formulas/first_order_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/17xmiho3-Hf0bveFaIIvTe2Dr_8VC2V93?usp=sharing)

## 3. Fitch proofs

Henceforth, both Text mode and LaTeX mode are available.  The latter prints out the LaTeX source code that can be compiled with the aid of `\usepackage{proofmood}`.  Truth table doesn't need this package.

1. Truth Table (`truth_table.ipynb`)  
[GitHub](./logical_formulas/truth_table.ipynb) | [Google Colab](https://colab.research.google.com/drive/1_CK9IwWhMy4DkOSCYxjeD5YkQyaiQyaw?usp=sharing)
1. Propositional Logic (`fitch_prop.ipynb`) Fitch proof editor and verifier for propositional logic.  
[GitHub](./proofs/fitch_prop.ipynb) | [Google Colab](https://colab.research.google.com/drive/1RjmIWlpfpVbrR4ijKEqMdlhSs5q3shBU?usp=sharing)
1. Tautologies (`tautologies.ipynb`) Fitch proofs for some important tautologies.  
[GitHub](./proofs/tautologies.ipynb) | [Google Colab](https://colab.research.google.com/drive/1k4-uz5QScpRPnUW0GE8-kztemDTNh47M?usp=sharing)

## 4. Automatic generation of Fitch proofs

1. Alpha-beta pruning  
Not used for the time being.  Nevertheless this is included here because I believe that this tree searching algorithm will be used later for Fitch proof trees.  
[GitHub](https://github.com/jhjeong314/CS_Math) | [Google Colab](https://colab.research.google.com/drive/1QBi6fV4Pq3wA9A7JKGV-WFBGeKWZVgeD?usp=sharing) 