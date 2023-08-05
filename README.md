# Proofmood


Proofmood is a computer logic system designed for Fitch calculus, encompassing propositional and first-order logic.

Presently, Proofmood is accessible at https://proofmood.mindconnect.cc, and the website operates on the LAMP (Linux, Apache, MySQL, PHP) stack. The logic engine behind Proofmood is implemented using JavaScript.

The inception of this project dates back to 2009. As of May 2023, I have made the decision to migrate to Django and completely rewrite the logic engine using Python.

To comprehend the contents of this repository, it would be beneficial to have a fundamental understanding of Python, Jupyter Notebook, and mathematical logic.

You can contact me at jhjeong314@gmail.com and/or treenote@snu.ac.kr.

---

## 0. Readme

1. Most `.ipynb` files in this repo are also uploaded to Google Colab, allowing you to run the code in your web browser.
1. The contents of `Document.pdf` provide an explanation of the fundamental theories that underlie this repository.


## 1. Arithmetic expressions

Before we start working on logical formulas, we prepare some tools for parsing and displaying the AST(abstract syntax tree) in various formats such as Polish notation, RPN, infix notation with $\LaTeX$ enabled, and bussproof style tree.

1. LaTeX in Jupyter Notebook (`latex_in_jupyternotebook.ipynb`)  
  [GitHub](./latex_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1JRn8m4_t77R-gJqjFSXiKaikWcDMQAnS?usp=sharing)
1. MathJax in Jupyter Notebook (`mathjax_in_jupyternotebook.ipynb`)  
  [GitHub](./mathjax_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1rywvvBl6WIMHzCdW-HeH69kbf9XYjxCW?usp=sharing)
1. Parser for a simple arithmetic grammar (`arith4parser.ipynb`)  
  [GitHub](./arith4parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1vpzjogSZi-QOx0QnBOxgPPFZkEJVKU1b?usp=sharing)
1. Parser for arithmetic with unary minus and postfix operators (`arith5parser.ipynb`)  
  [GitHub](./arith5parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/18niproAYizRP6BzWXYsCK6wGc0GJse1U?usp=sharing)
1. Parser for arithmetic with function symbols. (`arith6parser.ipynb`)  
  [GitHub](./arith6parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1eAV9i2jEN39hfL7RbOsKnIW7qi-YveJa?usp=sharing)
1. Bussproof style tree (`arith7parser.ipynb`)  
  [GitHub](./arith7parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1Rv_vqzg8BtrmRfc16FwVsPYh3zNR07LE?usp=sharing)

## 2. Logical formulas

Added a new showOption called `bussproof`. This option does not generate a diagram but instead produces LaTeX code that can be seamlessly incorporated into a LaTeX document. 
To ensure correct compilation of the source .tex file, it is necessary to include the `\usepackage{bussproofs}` command in the preamble.

1. Parser for Propositional Formulas (`propositional_logic_parser.ipynb`)  
  [GitHub](./propositional_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1G4jS1WhPSuLveu1V8ga5j857Bz9-9ZZY?usp=sharing)
1. Parser for First-order Formulas (`first_order_logic_parser.ipynb`)  
  [GitHub](./first_order_logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/17xmiho3-Hf0bveFaIIvTe2Dr_8VC2V93?usp=sharing)

## 3. Fitch proofs
