# This file is imported by logic_parser.ipynb.

# <expr> ::= { <term> "imp" } <term> | <term> { ( "iff" | "xor") <term> }
# <term> ::= <factor> { ("and" | "or") <factor> }
# <factor> ::= { "not" } '(' <expr> ')' | { "not" } <atom>
# <atom> ::= [A-Z] { [A-Za-z0-9_] } | "bot"

## (1/2) Parse ## ---------------------------------------------------------

import re

class Token:
  def __init__(self, value):
    self.value = value
    self.arity = None
    self.precedence = None
    # input value is guaranteed to be [a-zA-Z0-9()_]+
    if value in ("imp", "iff", "xor"):
      self.token_type = 'conn_arrow'
      self.arity = 2
      self.precedence = 1
    elif value in ("and", "or"):
      self.token_type = 'conn_2ary'
      self.arity = 2
      self.precedence = 2
    elif value == "not":
      self.token_type = "conn_1ary"
      self.arity = 1
      self.precedence = 3
    elif value == 'bot':
      self.token_type = 'conn_0ary'
      self.arity = 0
      self.precedence = 4
    elif value[0].isupper():
      self.token_type = 'prop_letter'
      self.precedence = 4
    elif value == "(":
      self.token_type = 'lparen'
    elif value == ")":
      self.token_type = 'rparen'
    else:
      raise ValueError(f"'{value}' is invalid (Token)")
  def __str__(self):
    return f"{self.value}({self.token_type})"


def tokenizer(input_text):
  connectives = ("imp", "iff", "xor", "and", "or", "not", "bot")
  tokens = []
  # Split the input text into a list of tokens at word boundries and whitespaces
  # then remove empty strings and strip off leading and trailing whitespaces.
  li = [s.strip() for s in re.split(r"\b|\s", input_text, re.ASCII) 
                  if s.strip()]
  for s in li: # s is a nonempty string
    if not s.isascii():
      raise ValueError(f"'{s}' is invalid (non-ASCII)")
    if not (s in connectives or
            re.match(r'^[A-Z][A-Za-z0-9_]*$', s) or  # propositional letter
            s in ("(", ")")):   
      raise ValueError(f"'{s}' is invalid (non-token)")
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
  LATEX_DICT = Node.LATEX_DICT
  
  # post-order traversal (unlike the other 3 methods)
  if(ast.children):
    children = [build_GNode(kid, xpos, ypos, ax, r) for kid in ast.children]
  else:
    children = []
  label = ast.token.value

  if ast.token.token_type == 'prop_letter':
    label = identifier_to_latex(label)
  else:
    label = LATEX_DICT[label]
  
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

def identifier_to_latex(instr):
  pos_underscore = instr.rfind('_')
  if pos_underscore >= 0:
    str1 = instr[:pos_underscore]
    str2 = instr[pos_underscore+1:]
    subscript = r"_{" + str2 + r"}" if str2 else ""
  else:
    str1 = instr
    subscript = ""

  if len(str1) > 1 and not str1.isdecimal():
    left_str = r"{\rm " + str1.replace("_", r"\_") + r"}"
  else: 
      left_str = str1

  return left_str + subscript

class Node:
  LATEX_DICT = dict([("not", r"\neg"), ("and", r"\wedge"), ("or", r"\vee"),
                     ("imp", r"\rightarrow"), ("iff", r"\leftrightarrow"),
                     ("xor", r"\nleftrightarrow"), ("bot", r"\bot")])

  def __init__(self, token, children=None):
    self.token = token # the node is labeled with a Token object
    self.children = children if children else [] # list of Node objects

  def __str__(self):
    return self.build_polish_notation()

  def build_polish_notation(self, opt=False):
    ret_str = f"{self.token}" if opt else f"{self.token.value}"
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
    ret_str += f"{self.token}" if opt else f"{self.token.value}"
    return ret_str
  
  def build_infix_latex(self):
    LATEX_DICT = self.LATEX_DICT

    if not self.children: 
      if self.token.token_type == 'prop_letter':
        # All but the last occurrence of an underscore in an identifier are escaped with a backslash.
        # Identifier string is romanized except the end substrings after the
        # last underscore, which are subscripted with _{}.

        return identifier_to_latex(self.token.value)
      else: # self.token.value could be 'bot'
        return LATEX_DICT[self.token.value]
    else: # self.token is a connective
      ret_str = ''
      if self.token.arity == 2:
        token_str = ' ' + LATEX_DICT[self.token.value] + ' '
        kid1, kid2 = self.children
        kid1_str = kid1.build_infix_latex()
        kid2_str = kid2.build_infix_latex()
        if self.token.precedence == 1: 
          # determine whether we need parentheses around kid1
          if kid1.token.precedence == 1:
            if self.token.value != kid1.token.value:
              kid1_str = f"({kid1_str})"
            else:
              if self.token.value == "imp":
                kid1_str = f"({kid1_str})"
              else:
                pass # iff and xor are associative
          # determine whether we need parentheses around kid2
          if kid2.token.precedence == 1:
            if self.token.value != kid2.token.value:
              kid2_str = f"({kid2_str})"
            else:
              pass # even 'imp' is right-associative
        else: # 'and', 'or' (precedence == 2)
          if(kid1.token.precedence > self.token.precedence):
            pass
          # determine whether we need parentheses around kid1
          elif kid1.token.precedence < self.token.precedence:
            kid1_str = f"({kid1_str})"
          elif self.token.value != kid1.token.value:
              kid1_str = f"({kid1_str})"
          # determine whether we need parentheses around kid2
          if kid2.token.precedence > self.token.precedence:
            pass
          elif kid2.token.precedence < self.token.precedence:
            kid2_str = f"({kid2_str})"
          elif self.token.value != kid2.token.value:
              kid2_str = f"({kid2_str})"
        ret_str += kid1_str + token_str + kid2_str
      else: # arity is 1
        token_str = LATEX_DICT[self.token.value] + ' ' 
        kid1 = self.children[0]
        kid1_str = kid1.build_infix_latex()
        # determine whether we need parentheses around kid1
        if kid1.token.precedence < self.token.precedence:
          kid1_str = f"({kid1_str})"
        else:
          pass
        ret_str += token_str + kid1_str

      return ret_str  
    
  def build_bussproof_rec(self):
    LATEX_DICT = self.LATEX_DICT

    if not self.children: 
      if self.token.token_type == 'prop_letter':
        label = identifier_to_latex(self.token.value)
      else: # self.token.value could be 'bot'
        label = LATEX_DICT[self.token.value]

      the_str = r"\AxiomC" + r"{$" + label + "$}\n"
    else: # self.token is a connective
      token_str = LATEX_DICT[self.token.value]
      if self.token.arity == 2:
        kid1, kid2 = self.children
        kid1_str = kid1.build_bussproof_rec()
        kid2_str = kid2.build_bussproof_rec()
        the_str = kid1_str + kid2_str + r"\BinaryInfC" + r"{$" + token_str + "$}\n"
      else: # arity is 1
        kid1 = self.children[0]
        kid1_str = kid1.build_bussproof_rec()
        the_str = kid1_str + r"\UnaryInfC" + r"{$" + token_str + "$}\n"

    return the_str

  def build_bussproof(self):
    the_str = self.build_bussproof_rec()

    return r"\begin{prooftree}" + "\n" + the_str + r"\end{prooftree}"
  
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

  def check_token_type(self, token_types) -> bool:
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
    
  def check_token_value(self, token_value: str) -> bool:
    # Check if self.current_token is of value token_value.
    token = self.current_token
    if token is None:
      return False
    elif token.value == token_value:
      return True
    else:
      return False
    
  def parse(self):
    return self.expr() 
  
  def expr(self):
    node = self.term()  

    while self.check_token_type('conn_arrow'): # 'imp', 'iff', 'xor'
      token = self.current_token
      if token is None:
        raise SyntaxError(f"Expected a token at {self.index}," +
                f" in expr(), but {self.current_token} is None.")
      self.advance()
      if token.value == 'imp':
        right_term = self.expr()
      else:
        right_term = self.term()
      
      node = Node(token, [node, right_term]) 
    
    return node
    
  def term(self):
    node = self.factor()

    while self.check_token_type('conn_2ary'): # 'and', 'or'
      token = self.current_token
      self.advance()
      right_factor = self.factor()
      node = Node(token, [node, right_factor]) # left associative

    return node

  def factor(self):
    if self.check_token_type('lparen'):
      self.advance()
      node = self.expr()
      if self.check_token_type('rparen'):
        self.advance()
      else:
        raise SyntaxError(f"Expected ')' at {self.index}," +
                          f" in factor(), but {self.current_token} is given.")
    elif self.check_token_type('conn_1ary'): # 'not'
      token = self.current_token 
      self.advance()
      right_factor = self.factor() # recursive call
      node = Node(token, [right_factor])
    else:
      node = self.atom()

    return node
        
  def atom(self):
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type(('conn_0ary', 'prop_letter')):
        self.advance()
        return Node(token)
      else:
        raise SyntaxError(f"Expected bot or prop_letter at {self.index}," +
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
    # Root's position is (0, 0). When rendering, we will shift the
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
