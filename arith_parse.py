# This file is imported by arith7parser.ipynb.

# <expr> ::= (<term> | <nterm>) { ("+" | "-") <term> }
# <nterm> ::= "-" { "-" } <term>
# <term> ::= <factor> { ("*" | "/") <factor> }
# <factor> ::= { <factor_exp> "^" } <factor_exp>
# <factor_exp> ::= <factor_post> { ("!" | "'") }
# <factor_post> ::= "(" <expr> ")"  | <func_call> | <atom>
# <func_call> ::= <func_symb> '(' <expr> {',' <expr>} ')' 
#   # 0-ary functions are not allowed
# <atom> ::= <identifier> | <numeral>
# <identifier> ::= <letter> { <letter> | <digit> }
# <letter> ::= [a-zA-Z] 
# <numeral> ::= <nonzero_digit> { <digit> }
# <digit> ::= [0-9]
# <nonzero_digit> :: = [1-9] 
# <func_symb> ::= "sin" | "cos" | "max" | "min" | "f"
#   # Function symbols with their arities can be set in Token class constructor.

## (1/2) Parse ## ---------------------------------------------------------

import re

class Token:
  def __init__(self, value):
    # You can put more function symbols here. 
    # For example, ('tan', 1), ('log', 1), ('choose', 2), ('g', 2), ('f1', 1).
    FUNCTION_SYMBOLS = dict([('sin', 1), ('cos', 1), ('max', 2), ('min', 2), ('f', 3)])

    self.value = value
    self.arity = None 
    self.precedence = None
    # input value is guaranteed to be a valid token
    if value == ",":
      self.token_type = 'comma'
    elif value in ("+", "-"):
      self.token_type = 'op_bin_1' # weak precedence
      self.precedence = 1
    elif value in ("*", "/"):
      self.token_type = 'op_bin_2' # medium precedence
      self.precedence = 2
    elif value == "(":
      self.token_type = 'lparen'
    elif value == ")":
      self.token_type = 'rparen'
    elif value in ("!", "'"):
      self.token_type = 'op_postfix' # strongest precedence
      self.precedence = 4
    elif value == "^":
      self.token_type = "op_bin_exp" # strong precedence
      self.precedence = 3
    elif value.isdecimal():
      self.token_type = 'numeral'
      self.precedence = 6
    elif value in FUNCTION_SYMBOLS:
        self.token_type = 'func_symb'
        self.arity = FUNCTION_SYMBOLS[value]
        self.precedence = 5
    elif value.isalnum() and value[0].isalpha():
      self.token_type = 'identifier'
      self.precedence = 6
    else:
      raise ValueError(f"'{value}' is invalid (Token)")
  
# There is a token_type which is called 'op_unary_prefix'. 
# It will be given to '-' during parsing. 
# It has precedence 1, the same as binary "-"'s precedence.
# During tokenization, '-' is given the provisional type 'op_bin_1'.
# This can only appear as the first token in an expression. 
# a * -b, a + -b, a ^ -b are all invalid. 
# a * (-b), a + (-b), a ^ (-b) are all valid. f(-x, -y) is valid too.

  def __str__(self):
    ret_str = f'{self.value} ({self.token_type})'
    if self.arity is not None:
      ret_str += f' arity: {self.arity}'
    return ret_str

def tokenizer(input_text):
  tokens = []
  # split the input text into a list of tokens at word boundries and whitespaces
  # then remove empty strings and strip off leading and trailing whitespaces
  li = [s.strip() for s in re.split(r"\b|\s", input_text, re.ASCII) 
                  if s.strip()]
  for s in li: # s is a string
    if not s.isascii():
      raise ValueError(f"'{s}' is invalid (non-ASCII)")
    if not (set(s).issubset("+-*/()!'^,") or  # operator or parenthesis or comma
            (s.isdecimal() and s[0]!='0') or  # numeral
            (s.isalnum() and s[0].isalpha())):   
                                              # identifier or function symbol
      raise ValueError(f"'{s}' is invalid (non-token)")
    if set(s).issubset("+-*/()!'^,") and len(s) > 1:
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

def build_GNode(ast, xpos, ypos, ax, r):
  # post-order traversal (unlike the other 3 methods)
  if(ast.children):
    children = [build_GNode(kid, xpos, ypos, ax, r) for kid in ast.children]
  else:
    children = []
  label = ast.token.value
  if ast.token.token_type == 'func_symb' and len(label) > 1:
    label = r'\operatorname{' + label + '}'
  elif ast.token.value == '^':
    label = r'\textasciicircum'
  txt = ax.text(xpos, ypos, '$' + label + '$', 
                ha='center', va='center', fontsize=6, alpha=0)
  return GNode(txt, ax, r, children=children)

def draw_ast(ast, verbose=False):
  import matplotlib.pyplot as plt

  plt.rcParams["mathtext.fontset"] = "cm" # cm = computer modern by Donald Knuth
  plt.rcParams["figure.dpi"] = 300 # default 100
  fig, ax = plt.subplots(1, 1, figsize=(1.5, 1))
  ax.set(aspect='equal')
  ax.set_xlim(0, 3) 
  ax.set_ylim(0, 2) 
  ax.axis('off')
  center_x = ax.get_xlim()[1] / 2
  center_y = ax.get_ylim()[1] / 2
  r = fig.canvas.get_renderer()

  tree = build_GNode(ast, center_x, center_y, ax, r)

  if verbose:
    print(tree)

  tree.draw_tree(plt)

class Node:
  def __init__(self, token, children=None):
    self.token = token # the node is labeled with a Token object
    self.children = children if children else [] # list of Node objects

  def __str__(self):
    return self.build_polish_notation()

  def build_polish_notation(self, opt=False):
    ret_str = f"{self.token.value}({self.token.token_type})" if opt \
      else f"{self.token.value}"
    if self.children:
      ret_str += ' '
    ret_str += ' '.join(child.build_polish_notation(opt) 
                        for child in self.children)
    return ret_str
  
  def build_RPN(self, opt=False):
    ret_str = ''
    if self.children:
      ret_str += ' '.join(child.build_RPN(opt) 
                          for child in self.children) + ' '
    ret_str += f"{self.token.value}({self.token.token_type})" if opt \
      else f"{self.token.value}"
    return ret_str
  
  def build_infix_latex(self):
    # This method is harder to implement than the other two, but not very much so.
    # Basically, we do recursion as we did everywhere else.
    # All we need is repeat
    #   root sub1 sub2 => (sub1) root (sub2)
    # recursively.  But we need to take care of the parentheses, for otherwise
    # we will get too many (unharmful but unnecessary) parentheses. 
    # In *(+(a, b), *(c, d)) => (a + b) * (c * d), we need the parentheses around
    # a + b, but not around c * d. This is because * has higher precedence than +.
    if not self.children: # leaf node, i.e. a numeral or an identifier
      return self.token.value
    else:
      # self.token.token_type == func_symbol | op_unary_prefix | op_bin_1 | 
      #                          op_bin_2 | op_bin_exp | op_postfix
      ret_str = ''
      if self.token.token_type == 'func_symb':
        label = self.token.value
        if(len(label) > 1):
          label = r'\operatorname{' + label + '}'
        ret_str += label + '('
        ret_str += ', '.join(kid.build_infix_latex() for kid in self.children) + ')'
      else: # self.token is an operator symbol
        if self.token.precedence == 1: # op_unary_prefix or op_bin_1
          if self.token.token_type == 'op_unary_prefix':
            kid1 = self.children[0]
            kid1_str = kid1.build_infix_latex()
            if kid1.token.precedence == 1:
              kid1_str = '(' + kid1_str + ')'
            # else pass
            ret_str += self.token.value + kid1_str
          else: # op_bin_1
            kid1, kid2 = self.children
            kid1_str = kid1.build_infix_latex()
            kid2_str = kid2.build_infix_latex()
            if self.token.value == '-' and kid2.token.precedence == 1:
              kid2_str = '(' + kid2_str + ')'
            # else pass
            ret_str += kid1_str + ' ' + self.token.value + ' ' + kid2_str
        elif self.token.precedence == 2: # op_bin_2
          kid1, kid2 = self.children
          kid1_str = kid1.build_infix_latex()
          kid2_str = kid2.build_infix_latex()
          if self.token.value == '/' and kid2.token.precedence == 2:
            kid2_str = '(' + kid2_str + ')'
          if kid1.token.precedence < self.token.precedence:
            kid1_str = '(' + kid1_str + ')'
          if kid2.token.precedence < self.token.precedence:
            kid2_str = '(' + kid2_str + ')'
          ret_str += kid1_str + ' ' + self.token.value + ' ' + kid2_str
        elif self.token.precedence == 3: # op_bin_exp
          kid1, kid2 = self.children
          kid1_str = kid1.build_infix_latex()
          kid2_str = kid2.build_infix_latex()
          if kid1.token.precedence <= self.token.precedence: 
            # <= instead of < because of right-associativity
            kid1_str = '(' + kid1_str + ')'
          if kid2.token.precedence < self.token.precedence:
            pass # In a^(b+c), we don't need parentheses around b+c when it's latexed.
          ret_str += kid1_str + ' ' + self.token.value + ' ' + '{' + kid2_str + '}'
        else: # precedenc==4. must be of type op_postfix
          kid1 = self.children[0]
          kid1_str = kid1.build_infix_latex()
          if kid1.token.precedence < self.token.precedence:
            kid1_str = '(' + kid1_str + ')'
          ret_str += kid1_str + self.token.value
      return ret_str

  def draw_tree(self, verbose=False):
    draw_ast(self, verbose)


class Parser:
  def __init__(self, tokens):
    self.tokens = tokens
    self.current_token = None
    self.index = -1
    self.advance()  # set self.current_token to 
                    # the first(i.e. self.index=0) element of tokens

  def advance(self): # increment self.index and set self.current_token
    self.index += 1
    if self.index < len(self.tokens):
      self.current_token = self.tokens[self.index]
    else:
      self.current_token = None

  def check_token_type(self, token_types):
    # token_types can be a string or a tuple of strings
    # Check if self.current_token is of type token_types if token_types is a string
    # or belongs to token_types if token_types is a tuple of strings.
    token = self.current_token
    if token is None:
      return False
    elif type(token_types) is not tuple: # must be a string in this case
        return token.token_type == token_types
    elif token.token_type in token_types:
      return True
    else:
      return False
    
  def check_token_value(self, token_value):
    # Check if self.current_token is of value token_value.
    token = self.current_token
    if token is None:
      return False
    elif token.value == token_value:
      return True
    else:
      return False
    
  def parse(self):
    return self.expr() # expr() corresponds to the starting symbol <expr>

  def expr(self):
    if self.check_token_value('-'): # unary minus
      node = self.nterm() # negative term
    else: # ordinary term
      node = self.term()  

    while self.check_token_type('op_bin_1'): # '+' or '-'
      # If we are at '+' in "a + b * c - ..." then the next token is '-'
      # because we will consume tokens by self.advance() and self.term().
      token = self.current_token
      self.advance()
      right_term = self.term()
      node = Node(token, [node, right_term]) # left associative
    
    return node
  
  def nterm(self):
    token = self.current_token 
    # For the first visit only, token.value == '-' is  guaranteed
    #   because we have checked it in self.expr().
    # But for subsequent recursive calls it can be otherwise.
    if(token is None or token.value != '-'):
      node = self.term()
    else:
      token.token_type = 'op_unary_prefix'
      self.advance()
      unary_node = self.nterm() # recursive call
      node = Node(token, [unary_node])

    return node
  
  def term(self):
    node = self.factor()

    while self.check_token_type('op_bin_2'): # '*' or '/'
      token = self.current_token
      self.advance()
      right_factor = self.factor()
      node = Node(token, [node, right_factor])

    return node

  def factor(self):
    node = self.factor_exp()

    if self.check_token_type('op_bin_exp'): # '^'
      token = self.current_token
      self.advance()
      right_factor = self.factor() # recursive call for right associativity
      node = Node(token, [node, right_factor])

    return node
  
  def factor_exp(self):
    node = self.factor_postfix()

    while self.check_token_type('op_postfix'):
      token = self.current_token
      self.advance()
      node = Node(token, [node])

    return node

  def factor_postfix(self):
    if self.check_token_type('lparen'):
      self.advance()
      node = self.expr()
      if self.check_token_type('rparen'):
        self.advance()
      else:
        raise SyntaxError(f"Expected ')' after expression at {self.index} " +
                          f"in factor_postfix(), but {self.current_token} is given.")
    elif self.check_token_type('func_symb'):
      node = self.func_call()
    else:
      node = self.atom()

    return node

  def func_call(self):
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type('func_symb'):
        self.advance()
        if self.check_token_type('lparen'):
          self.advance()
          args = []

          while True:
            args.append(self.expr())
            if self.check_token_type('comma'):
              self.advance()
            elif self.check_token_type('rparen'):
              break
            else:
              raise SyntaxError(f"Expected ',' or ')' after function argument at " +
                                f"{self.index} in, but {self.current_token} is given.")
          
          # arity check
          if token.arity is None or token.arity != len(args):
            raise SyntaxError(f"Function {token.value} expects {token.arity} " +
                              f"arguments, but {len(args)} were given")

          self.advance()
          return Node(token, args)
        
        else:
          raise SyntaxError(f"Expected '(' after function symbol at {self.index}" +
                            f" in func_call(), but {self.current_token} is given.")
      else:
        raise SyntaxError(f"Expected function symbol at {self.index} in" +
                          f" func_call(), but {token} is given.")
    else:
      raise SyntaxError("Unexpected end of input, in func_call()")
      
  def atom(self):
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type(('numeral', 'identifier')):
        self.advance()
        return Node(token)
      else:
        raise SyntaxError(f"Expected numeral or identifier at {self.index}," +
                          f" in atom(), but {token} is given.")
    else:
      raise SyntaxError("Unexpected end of input, in atom()")
    
def parse_text(input_text):
  tokens = tokenizer(input_text)
  parser = Parser(tokens)
  ast = parser.parse() # ast = Abstract Syntax Tree
  if parser.current_token is not None:
    raise SyntaxError(f"Unexpected token {parser.current_token} at {parser.index}," +
                      f" in parse_text(). Expected end of input.")
  return ast

## (2/2) Draw bussproof style Trees ## ------------------------------------

from matplotlib import pyplot as plt

class Tbox: # text object together with its position and size
  def __init__(self, txt, ax, r):
    # txt is a text object
    # r is a renderer
    self.txt = txt # matplotlib.text.Text object
      # txt.get_text() is the label (latex source string)
    bbox = txt.get_window_extent(renderer=r) # unit: pixel
    bbox_d = bbox.transformed(ax.transData.inverted()) # unit: data coordinate
    x, y = txt.get_position()
    self.x = x
    self.y = y
    self.width = bbox_d.width
    self.height = bbox_d.height

  def __str__(self):
    return f"x = {self.x:.3f}, y = {self.y:.3f}, w = {self.width:.3f}, h = {self.height:.3f}"
    
class GNode: # graph node
  def __init__(self, txt, ax, r, unit_len = 0.12, kx=3, ky=1, overhang=0.14, children=None):
    # txt = ax.text(pos_x, pos_y, string, ..) is a text object
    # r is a renderer
    # dx is the horizontal distances between the children
    # dy is the vertical distance between the root and the children    
    # children is a list of Node objects    
    # Roote's position is (0, 0). When rendering, we will shift the
    # node's center to the center of the figure.
    # The root and each child's position is relative to the center of the node.
    
    self.parent = None # This changes later iff self is not the real(one and only) root.
    self.x = self.y = 0
    self.root = tbox = Tbox(txt, ax, r)
    self.children = None
    self.unit_height = unit_len
    self.overhang = overhang
    # Both (self.x, self.y) and (self.root.x, self.root.y) are positions of 
    # the root of self.  
    # The meaning of (self.x, self.y) depends on self.parent.
    # If self.parent is None, then (self.x, self.y) is not used at all.
    # If self.parent is not None, then (self.x, self.y) is the position of the root of self
    # relative to the root of self.parent.
    # (self.root.x, self.root.y) has meaning iff self.parent is None.
    # It is the position (x, y) given when the text object was created by ax.text(x, y, ...) 
    # Normally it is (center_x, center_y) of the axis.

    dx = kx * unit_len
    dy = ky * unit_len
    unit_height = self.unit_height # height of each node (considered as a rectangle)
    if children:
      self.children = children
      # Compute the total width of the children.
      tot_width = sum([kid.width for kid in children]) + (len(children)-1)*dx
      self.width = tot_width
      # Compute the total height of the node
      max_height = max([kid.height for kid in children])
      tot_height = max_height + dy + unit_height
      self.height = tot_height
      # Get the position of each kid's root relative to the root of self.
      # dlrkids = distance between the leftmost kid's root and the rightmost kid's root
      #           = tot_width - (children[0].width + children[-1].width)/2
      # xvec = [-dlrkids/2, += children[0].width/2 + children[1].width/2 + dx, += ...]
      # xvec[-1] must be dlrkids/2
      # y = dy
      wl = children[0].width # width of the leftmost child
      wr = children[-1].width # width of the rightmost child
      dlrkids = tot_width - (wl + wr)/2
      for i, kid in enumerate(children):
        kid.parent = self
        kid.y = dy + unit_height
        if i==0:
          kid.x = -dlrkids/2 
        else:
          kid.x = children[i-1].x + children[i-1].width/2 + dx + children[i].width/2
      
      assert abs(children[-1].x - dlrkids/2) < 1e-6, "the last child's x is wrong"

    else:
      self.children = []
      self.width = tbox.width
      self.height = unit_height
    
  def __str__(self):
    return self.get_str()
  
  def get_str(self):
    # recursively print the tree
    s = (f"root: {self.root.txt.get_text()[1:-1]}, " +
         f"position: ({self.x:.3f}, {self.y:.3f}), " +
         f"width: {self.width:.3f}, height: {self.height:.3f}\n")
    if self.children:
      for kid in self.children:
        s += kid.get_str() # should revise using join()
    return s
   
  def draw_tree(self, plt1):
    # Draw the root.
    if self.parent is None:
      x_ref, y_ref = (self.root.x, self.root.y) # normally (center_x, center_y)
      if self.children: # Then we shift the root down and maybe left/right too
          # so that the center of the whole tree coincides with the center of the axis.
        node_left = self.children[0]
        node_right = self.children[-1]
        wl = node_left.width
        wr = node_right.width
        x = x_ref + (wl - wr)/4
        y = y_ref - self.height/2 + self.unit_height/2
        self.root.txt.set_position((x, y))
        self.x, self.y = (x, y)
        # draw the horizontal line
        plt1.hlines(y + self.unit_height, x+node_left.x-self.overhang, 
                    x+node_right.x+self.overhang, linewidth=0.2, color='black')
      else: # Then there is no need to shift the root.
        pass
      self.root.txt.set_alpha(1)
    else:
      x_ref, y_ref = (self.parent.x, self.parent.y)
      x = x_ref + self.x
      y = y_ref + self.y
      self.root.txt.set_position((x, y))
      self.x, self.y = (x, y)
      self.root.txt.set_alpha(1)

    # Draw the children.
    if self.children:
      # draw horizontal line
      node_left = self.children[0]
      node_right = self.children[-1]
      plt1.hlines(self.y + self.unit_height, 
                   self.x + node_left.x - self.overhang, self.x + node_right.x + self.overhang,
                   linewidth=0.2, color='black')
      # draw subtrees
      for kid in self.children:
        kid.draw_tree(plt1)
