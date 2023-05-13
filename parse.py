
# This is just a .py export of the notebook arith4parser.ipynb. 


# %% [markdown]
# Arith4 is a simple grammar for arithmetic.
# We'll build a parser for this grammar.
# 
# ```
# <expr> ::= <expr> ("+" | "-") <term> | <term>
# <term> ::= <term> ("*" | "/") <factor> | <factor>
# <factor> ::= "(" <expr> ")" | <atom>
# <atom> ::= <identifier> | <numeral>
# <identifier> ::= <letter> { <letter>  }
# <letter> ::= [a-z] 
# <numeral> ::= [1-9] { [0-9] }
# ```

class Token:
  def __init__(self, value):
    self.value = value
    # input value is guaranteed to be a valid token
    if value in ("+", "-"):
      self.token_type = 'op_type1' # precedence 1
    elif value in ("*", "/"):
      self.token_type = 'op_type2' # precedence 2
    elif value == "(":
      self.token_type = 'lparen'
    elif value == ")":
      self.token_type = 'rparen'
    elif value.isdecimal():
      self.token_type = 'numeral'
    elif value.isalpha():
      self.token_type = 'identifier'
    else:
      raise ValueError(f"'{value}' is invalid token")
  
  def __str__(self):
    return f'{self.value} ({self.token_type})'

import re

def tokenizer(input_text):
  tokens = []
  # split the input text into a list of tokens at word boundries and whitespaces
  # then remove empty strings and strip off leading and trailing whitespaces
  li = [s.strip() for s in re.split(r"\b|\s", input_text, re.ASCII) 
                  if s.strip()]
  for s in li: # s is a string
    if not s.isascii():
      raise ValueError(f"'{s}' is invalid (non-ASCII)")
    if not (set(s).issubset("+-*/") or        # operator
            (s.isdecimal() and s[0]!='0') or  # numeral
            (s.isalpha() and s.islower())):   # identifier
      raise ValueError(f"'{s}' is invalid (non-token)")
    if set(s).issubset("+-*/") and len(s) > 1:
      # split string of consecutive operators into individual characters
      for c in s: # c is an operator character
        tokens.append(Token(c))
    else:
      tokens.append(Token(s))
  
  return tokens

def testTokenizer(input_text):
  try:
    tokens = tokenizer(input_text)
  except ValueError as e:
    print(f"Tokenizer: {e}")
  else:
    for t in tokens:
      print(t)

class Node:
    def __init__(self, token, children=None):
        self.token = token
        self.children = children if children else []

    def __str__(self):
        return self.build_polish_notation()

    def build_polish_notation(self):
        if not self.children:
            return str(self.token.value)
        
        notation = f"{self.token.value} "
        notation += ' '.join(child.build_polish_notation() for child in self.children)
        return notation

class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.current_token = None
        self.index = -1
        self.advance()

    def advance(self):
        self.index += 1
        if self.index < len(self.tokens):
            self.current_token = self.tokens[self.index]
        else:
            self.current_token = None

    def parse(self):
        return self.expr()

    def expr(self):
        node = self.term()

        while self.current_token is not None and self.current_token.token_type in ('op_type1'):
            token = self.current_token
            self.advance()

            right = self.term()
            node = Node(token, [node, right])

        return node

    def term(self):
        node = self.factor()

        while self.current_token is not None and self.current_token.token_type in ('op_type2'):
            token = self.current_token
            self.advance()

            right = self.factor()
            node = Node(token, [node, right])

        return node

    def factor(self):
        if self.current_token is not None and self.current_token.token_type == 'lparen':
            self.advance()
            node = self.expr()
            if self.current_token is not None and self.current_token.token_type == 'rparen':
                self.advance()
            else:
                raise SyntaxError("Expected ')' after expression.")
        else:
            node = Node(self.current_token)
            self.advance()

        return node

def parse_input(input_text):
    tokens = tokenizer(input_text)
    parser = Parser(tokens)
    ast = parser.parse()
    return ast

input_text = "(a + b) * c"
ast = parse_input(input_text)
print(ast)




