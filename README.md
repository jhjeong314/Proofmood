# Proofmood


Proofmood is a computer logic system designed for Fitch calculus, encompassing propositional and first-order logic.

Presently, Proofmood is accessible at https://proofmood.mindconnect.cc, and the website operates on the LAMP (Linux, Apache, MySQL, PHP) stack. The logic engine behind Proofmood is implemented using JavaScript.

The inception of this project dates back to 2009. As of May 2023, I have made the decision to migrate to Django and completely rewrite the logic engine using Python.

To comprehend the contents of this repository, it would be beneficial to have a fundamental understanding of Python, Jupyter Notebook, and mathematical logic.

You can contact me at jhjeong314@gmail.com and/or treenote@snu.ac.kr.

---

## 0. Readme

Most `.ipynb` files are uploaded to Google Colab, allowing you to run the code in your web browser.

## 1. Arithmetic expressions

Before we start working on logical formulas, we prepare some tools for parsing and displaying the AST(abstract syntax tree) in various formats such as Polish notation, RPN, infix notation with $\LaTeX$ enabled, and bussproof style tree.

1. LaTeX in Jupyter Notebook [GitHub](./latex_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1JRn8m4_t77R-gJqjFSXiKaikWcDMQAnS?usp=sharing)
1. MathJax in Jupyter Notebook [GitHub](./mathjax_in_jupyternotebook.ipynb) | [Google Colab](https://colab.research.google.com/drive/1rywvvBl6WIMHzCdW-HeH69kbf9XYjxCW?usp=sharing)
1. Parser for a simple arithmetic grammar [GitHub](./arith4parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1vpzjogSZi-QOx0QnBOxgPPFZkEJVKU1b?usp=sharing)
1. Parser for arithmetic with unary minus and postfix operators. [GitHub](./arith5parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/18niproAYizRP6BzWXYsCK6wGc0GJse1U?usp=sharing)
1. Parser for arithmetic with function symbols. [GitHub](./arith6parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1eAV9i2jEN39hfL7RbOsKnIW7qi-YveJa?usp=sharing)
1. Bussproof style tree [GitHub](./arith7parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1Rv_vqzg8BtrmRfc16FwVsPYh3zNR07LE?usp=sharing)

## 2. Logical formulas

1. Parser for Propositional Formulas [GitHub](./logic_parser.ipynb) | [Google Colab](https://colab.research.google.com/drive/1ZlanSUrOCbLW0mJgMsUDdV8bF4B0Ab66?usp=sharing)

## 3. Fitch proofs
