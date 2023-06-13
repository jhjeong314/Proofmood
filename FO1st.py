# This file is imported by FO_parser1st.ipynb.

## (1/3) Tokenization ## ----------------------------------------------

#region Tokenization comments
#### Constants

# emptyset, infty

#### Function symbols

# binary infix function symbols:
#   precedence 1: +, -
#   precedence 2: *, /, %
#   precedence 3: ^
# unary prefix function symbols:
#   precedence 1: -
# unary postfix function symbols:
#   precedence 4: !, ', ^#, ^+, ^-, ^*, ^o, ^inv
# all other functions are n-ary prefix function symbols with n >= 1

# Certain symbols can be found in multiple categories. In such instances,
# the symbol's type and arity are initially assigned during tokenization 
# and later confirmed during parsing.

# The appearance of a symbol can vary depending on its type. For example, 
# the symbol "*" is typically displayed as an infix operator. However, 
# when used as a postfix operator, it is rendered as a superscript.

#### Predicate symbols

# binary infix predicate symbols: (precedences are all the same)
#   !=, <, <=, >, >=
#   in, nin, subseteq, nsubseteq, subsetneqq, 
#   supseteq, nsupseteq, supsetneqq, divides, ndivides,
#   sim, simeq, cong, equiv, approx
# all other predicates are n-ary prefix predicate symbols with n >= 0

#### Rendering

# We will use LaTeX for rendering. Once a formula is parsed, it is natural 
# to render it in polish notation or RPN(reverse polish notation).  But for
# human readers, infix notation is more natural.  So we need to convert
# the parsed tree back into infix notation---but this time we use LaTeXed
# token values.  Or we draw a tree diagram for the parsed tree(AST), in which 
# the nodes are labeled with the LaTeXed token values.

#### Precedence

# Precedences are used to determine the order of parsing and/or evaluation.
# The higher the precedence, the earlier the parsing and/or evaluation.
# The precedence of a token have meaning only among tokens of the same type
# as follows: Parenthesis > Function > Predicate > Quantifiers > Connectives

#### Associativity

# Syntactic associativity is used to determine the order of parsing.
# Left associativity means a op b op c = (a op b) op c.
# Right associativity means a op b op c = a op (b op c).
# Most operators are left associative.
# Right associativity is used for exponentiation(function) and 
# implication(connective).  Unary prefix operators are right associative too
# but this is trivial because they are always followed by a term.
# Semantic associativity is not relevant in parsing.
# But it is relevant in rendering. For instance, you don't need parentheses
# in A and B and C when rendering, although it is parsed as (A and B) and C 
# by the default left associativity.
# On the other hand, A and B or C is a legal expression but should be 
# rendered as (A and B) or C because it is parsed this way by the default
# left associativity.

#endregion

import re

class Token:
  CONSTS = [ "emptyset", "infty" ]
  OPER_PRE = [ "-" ]
  OPER_POST = [ "!", "'", "^#", "^+", "^-", "^*", "^o", "^inv" ]
  OPER_IN_1 = [ "+", "-", "cap", "cup", "oplus" ]
  OPER_IN_2 = [ "*", "/", "%", "times", "div", "otimes", "cdot" ]
  OPER_IN_3 = [ "^" ]
  PRED_IN = [ "!=", "<", "<=", ">", ">=", "in", "nin", "subseteq",
              "nsubseteq", "subsetneqq", "supseteq", "nsupseteq",
              "supsetneqq", "divides", "ndivides", "sim", "simeq",
              "cong", "equiv", "approx" ]
  RESERVED_WORDS = set(CONSTS + OPER_PRE + OPER_POST + OPER_IN_1 + 
                      OPER_IN_2 + OPER_IN_3 + PRED_IN)
  SPECIAL_CHARS = "-!'^#+*/%=<>()[]{},"
  FMLA_TOKENS = ("pred_pre", "pred_in", "equality", "prop_letter", 
    'conn_0ary') # an expression is a formula iff it has a token in FMLA_TOKENS
  FMLA_ROOTS = FMLA_TOKENS + ("conn_1ary", "conn_2ary", "conn_arrow", 
    "quantifier") # a parsed node is a formula iff it has a token in FMLA_ROOTS

  def __init__(self, value):
    CONSTS = self.CONSTS
    OPER_PRE = self.OPER_PRE
    OPER_POST = self.OPER_POST
    OPER_IN_1 = self.OPER_IN_1
    OPER_IN_2 = self.OPER_IN_2
    OPER_IN_3 = self.OPER_IN_3
    PRED_IN = self.PRED_IN

    self.value = value # a string
    self.token_type = None
    self.arity = None
    self.precedence = None
    # reserved words (equality, connectives, quantifiers, parentheses, comma)
    if value == "=":
      self.token_type = 'equality'
    elif value in ("imp", "iff", "xor"):
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
      self.precedence = 9
    elif value in ("forall", "exists"):
      self.token_type = 'quantifier'
      self.arity = 1
      self.precedence = 4
    elif value == "(":
      self.token_type = 'lparen'
    elif value == ")":
      self.token_type = 'rparen'
    elif value == ",":
      self.token_type = 'comma'
    # reserved words (constants)
    elif value in CONSTS:
      self.token_type = 'const'
      self.precedence = 9
    # reserved words (function symbols)
    elif value in OPER_IN_1:
      self.token_type = 'oper_in_1'
      self.arity = 2
      self.precedence = 1
    elif value in OPER_IN_2:
      self.token_type = 'oper_in_2'
      self.arity = 2
      self.precedence = 2
    elif value in OPER_IN_3:
      self.token_type = 'oper_in_3'
      self.arity = 2
      self.precedence = 3
    elif value in OPER_PRE:
      self.token_type = 'oper_pre' # unary '-'
      self.arity = 1
      self.precedence = 1
    elif value in OPER_POST:
      self.token_type = 'oper_post'
      self.arity = 1
      self.precedence = 4
    # reserved words (predicate symbols)
    elif value in PRED_IN:
      self.token_type = 'pred_in'
      self.arity = 2
    else:
      # numeral, variable, constant, func_pre, pred_pre       
      len_s = len(value)
      if self.isnumeral(value):
        self.token_type = 'numeral'
      elif value[0] in "uvw" + "xyz" + "ijk" + "lmn":
        # we use concatenation to avoid the stupid cSpell warning
        if (len_s==1 or 
            (len_s >= 3 and value[1]=='_' 
             and Token.isword(value[2:], "decimal"))):
          self.token_type = 'var'
        else:
          raise ValueError(f"'{value}' is invalid variable symbol (Token)")
      elif value[0] in "abcde" :
        if len_s==1 or Token.isword(value[1:]):
          self.token_type = 'const'
        else:
          raise ValueError(f"'{value}' is invalid constant symbol (Token)")        
      elif value[0] in "fgh":
        if len_s==1 or Token.isword(value[1:]):
          self.token_type = 'func_pre'
          self.arity = self.get_arity(value)
        else:
          raise ValueError(f"'{value}' is invalid function symbol (Token)")
      elif Token.isword(value, "upper"):
        if len_s==1 or Token.isword(value[1:]):
          self.arity = self.get_arity(value)
          self.token_type = 'pred_pre' if self.arity > 0 else 'prop_letter'
        else:
          raise ValueError(f"'{value}' is invalid predicate symbol (Token)")
      else:
        raise ValueError(f"'{value}' is invalid (Token)")
  
  @staticmethod
  def isnumeral(s: str) -> bool:
    # str is assumed to be isascii().
    return s.isdecimal() and (len(s) == 1 or s[0]!='0')
  
  @staticmethod
  def isword(s: str, opt: str="all") -> bool:
    if(not s.replace('_','').isalnum()):
      return False
    if(opt=="alpha"):
      return s[0].isalpha()
    elif(opt=="lower"):
      return s[0].islower()
    elif(opt=="upper"):
      return s[0].isupper()
    elif(opt=="decimal"):
      return s.isdecimal()
    elif(opt=="numeral"):
      return Token.isnumeral(s)
    else: # opt=="all"
      return True
    
  @staticmethod
  def get_arity(value: str) -> int:
    #region cmt
    # Get arity of a function symbol (starts with [fgh]) 
    #   or a predicate symbol (starts with [A-Z]).
    # If the last character is a decimal digit, and if it does not follow
    # the underscore character, then it is the arity.
    # Otherwise, if the first character is [fgh], it is 1.
    #   Otherwise, it is 0. (prop_letter)
    # Arity 0 is not allowed for function symbols because it is
    #   reserved for constants.
    # Arity cannot exceed 9 unless it is declared explicitly in
    #   other ways.
    # Arities are not rendered because it can be inferred from
    #   the number of arguments.
    #endregion cmt
    if (not (d := value[-1]).isdecimal()
        or (len(value) >= 2 and value[-2] == '_')):
      if value[0] in "fgh":
        return 1 # unary function
      elif value[0].isupper():
        return 0 # propositional letter
      else:
        raise ValueError(
          f"'{value}' is invalid in get_arity(), " + 
            "function or predicate symbol expected"
        )
    else:
      if value[0] in "fgh" and d=="0":
        raise ValueError(
          f"'{value}' is invalid, 0-ary function not allowed (Token)"
        )
      else:
        return int(d)

  def __str__(self):
    if self.arity is not None:
      s_arity = f", arity={self.arity}"
    else:
      s_arity = ""
    if self.precedence is not None:
      s_precedence = f", precedence={self.precedence}"
    else:
      s_precedence = ""

    return f"{self.value} ({self.token_type}{s_arity}{s_precedence})"

#region token class helper
def tokenizer(input_text):
  import re
  tokens = []
  # split the input text into a list of tokens at word boundaries and 
  # whitespaces then remove empty strings and strip off leading and 
  # trailing whitespaces
  li = [s.strip() for s in re.split(r"\b|\s", input_text, re.ASCII) 
                  if s.strip()]
  for s in li: # s is a string
    if not s.isascii():
      raise ValueError(f"'{s}' is invalid (non-ASCII)")
    if not (set(s).issubset(Token.SPECIAL_CHARS) or 
            Token.isnumeral(s) or Token.isword(s)):   
      raise ValueError(f"'{s}' is invalid (non-token)")
    
    if set(s).issubset(Token.SPECIAL_CHARS) and len(s) > 1:
      # split string of consecutive special chars into 
      # individual characters or !=, <=, >=, ^*, ^+, ^-, ^#
      for c in s: # c is a special char
        if c == "=" and tokens and tokens[-1].value in "!<>":
          token1 = tokens.pop()
          token1.value += c
          tokens.append(Token(token1.value))
        elif (c in ("*", "+", "-", "#") and 
              tokens  and tokens[-1].value=="^"):
          token1 = tokens.pop()
          token1.value += c
          tokens.append(Token(token1.value))
        else:
          tokens.append(Token(c))
    elif s in ("o", "inv"): 
      # '^o' and '^inv' are postfix unary function symbols
      if tokens and tokens[-1].value=="^":
        token1 = tokens.pop()
        token1.value += s
        tokens.append(Token(token1.value))
      else:
        tokens.append(Token(s))
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

def print_in_chunk(li, chunk_size=5): # li is any iterable
  for i, s in enumerate(li):
    print(s, end=" " if i % chunk_size != chunk_size-1 else "\n")
#endregion token class helper

## (2/3) Parsing ## ---------------------------------------------------

#region Comment
# <formula> ::= { <comp_fmla1> "imp" } <comp_fmla1> | 
#                 <comp_fmla1> { ( "iff" | "xor") <comp_fmla1> }
# <comp_fmla1> ::= <comp_fmla2> { ("and" | "or") <comp_fmla2> }
# <comp_fmla2> ::= { ("not" | <quantifier>) } '(' <formula> ')' | 
#                  { ("not" | <quantifier>) } <atom>
# <quantifier> ::= "forall" | "exists"
# <atom> ::= "bot" | <prop_letter> | 
#            <pred_pre> "(" <term> {',' <term>} ")" |
#            <term> <pred_in> <term>

# # The "bot" connective is typically classified as a compound formula, 
# # but when it comes to parsing, it is treated as an atom.
# # prop_letter, pred_pre, pred_in are defined in the Token class.

# <term> ::= (<term1> | <nterm1>) { <oper_in_1> <term1> }
# <nterm1> ::= <oper_pre> { <oper_pre> } <term1>
# <term1> ::= <factor> { <oper_in_2> <factor> }
# <factor> ::= { <factor_exp> <oper_in_3> } <factor_exp>
# <factor_exp> ::= <factor_postfix> { <oper_postfix> }
# <factor_postfix> ::= "(" <term> ")"  | <func_call> | <identifier>
# <func_call> ::= <func_pre> '(' <term> {',' <term>} ')' 
# <identifier> ::= <const> | <numeral> | <var>

# # oper_in_1, oper_pre, oper_in_2, oper_in_3, oper_post, 
# #   func_pre, const, numeral, var are defined in the Token class.
#endregion

class Node:
  LATEX_DICT = dict(
    [("not", r"\neg"), ("and", r"\wedge"), ("or", r"\vee"),
    ("imp", r"\rightarrow"), ("iff", r"\leftrightarrow"),
    ("xor", r"\nleftrightarrow"), ("bot", r"\bot"), ("emptyset", r"\varnothing"),
    ("^o", r"^{\circ}"), ("^inv", r"^{-1}")])
  #region Comment
  # Other than the above and '^', for all reserved tokens, just use 
  # ("token.value", r"\token.value") for the mapping.
  # Special care is needed for '^'. See the build_infix_latex_formula() 
  #   method below.
  # For user-defined tokens, use the following static method ident2latex().
  #endregion

  @staticmethod
  def ident2latex(token: Token) -> str:
    #region Comment
    # Identifier means the token.value when token.token_type is "var",
    # "const", "numeral", "func_pre", "pred_pre".
    # All but the last occurrence of an underscore in the string
    # are escaped with a backslash.
    # Identifier string is romanized except the end substrings after 
    # the last underscore, which are subscripted with _{}.
    # If the last character is a decimal and the previous char is not
    # underscore, then it is not rendered because it is interpreted as 
    # the arity of the symbol.
    #endregion
    label = token.value
    pos_underscore = label.rfind('_')
    if (label[-1].isdecimal() and 
        token.token_type in ("func_pre", "pred_pre") and
        (pos_underscore < 0 or pos_underscore != len(label)-2)):
      label = label[:-1] # chop-off the last character
    
    if pos_underscore >= 0: # underscore exists in the identifier
      str1 = label[:pos_underscore]
      str2 = label[pos_underscore+1:]
      if len(str1) > 1:
        str1 = r"{\rm " + str1.replace("_", r"\_") + r"}"
      if str2:
        ret_val = str1 + r"_{" + str2 + r"}"
        # if there is no character after the last underscore, 
        # the last underscore is not rendered
      else:
        ret_val = str1
    else: # no underscore in the identifier
      str1 = label
      if len(str1) > 1:
        ret_val = r"{\rm " + str1 + r"}"
      else:
        ret_val = str1

    return ret_val

  def __init__(self, token, children=None):
    self.token = token # the node is labeled with a Token object
    self.children = children if children else [] # list of Node objects
    self.type = ('formula' if self.token.token_type in Token.FMLA_ROOTS 
                           else 'term')

  def __str__(self):
    return self.build_polish_notation()

  def build_polish_notation(self, operOpt=False):
    ret_str = f"{self.token}" if operOpt else f"{self.token.value}"
    if self.children:
      ret_str += ' '
      ret_str += ' '.join(child.build_polish_notation(operOpt) 
                        for child in self.children)
    return ret_str
  
  def build_RPN(self, operOpt=False):
    ret_str = ''
    if self.children:
      ret_str += ' '.join(child.build_RPN(operOpt) 
                          for child in self.children) + ' '
      
    ret_str += f"{self.token}" if operOpt else f"{self.token.value}"
    
    return ret_str

  def build_infix_latex(self):
    if(self.type == 'term'):
      return self.build_infix_latex_term()
    else: # self.type == 'formula'
      return self.build_infix_latex_formula()
    
  def build_infix_latex_term(self):
    LATEX_DICT = self.LATEX_DICT
    if not self.children: # leaf node ::= variable | const | numeral
      return self.ident2latex(self.token)
    else: # non-leaf node
      # token_type ::= func_pre | oper_in_1 | oper_in_2 | oper_in_3 |
      #                oper_pre | oper_post 
      ret_str = ''
      if self.token.token_type == 'func_pre':
        label = self.ident2latex(self.token)
        args = ', '.join(kid.build_infix_latex() for kid in self.children)
        ret_str += label + '(' + args + ')'
      else: # token is an operator with various arities and precedences
        if self.token.precedence == 1: 
          # oper_pre(unary) or oper_in_1(binary, +, -, cap, cup, oplus)
          if self.token.token_type == 'oper_pre':
            kid1 = self.children[0]
            kid1_str = kid1.build_infix_latex()
            if kid1.token.precedence == 1:
              kid1_str = '(' + kid1_str + ')'
            # else pass
            ret_str += self.token.value + kid1_str
          else: # oper_in_1
            kid1, kid2 = self.children
            kid1_str = kid1.build_infix_latex()
            kid2_str = kid2.build_infix_latex()
            if ((self.token.value == '-' and kid2.token.precedence == 1) or
                kid2.token.token_type == 'oper_pre'):
              kid2_str = '(' + kid2_str + ')'
            # else pass
            ret_str += kid1_str + ' ' + self.token.value + ' ' + kid2_str
        elif self.token.precedence == 2: # oper_in_2
          pass

      return ret_str

  def build_infix_latex_formula(self):  
    LATEX_DICT = self.LATEX_DICT

    if not self.children: # 'prop_letter' or 'conn_0ary'
      if self.token.token_type == 'prop_letter':
        return self.ident2latex(self.token)
      else: # self.token.value must be 'bot'
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
        label = self.ident2latex(self.token)
      else: # self.token.value could be 'bot'
        label = LATEX_DICT[self.token.value]

      the_str = r"\AxiomC" + r"{$" + label + "$}\n"
    else: # self.token is a connective
      token_str = LATEX_DICT[self.token.value]
      if self.token.arity == 2:
        kid1, kid2 = self.children
        kid1_str = kid1.build_bussproof_rec()
        kid2_str = kid2.build_bussproof_rec()
        the_str = (kid1_str + kid2_str + r"\BinaryInfC" + r"{$" + 
                   token_str + "$}\n")
      else: # arity is 1
        kid1 = self.children[0]
        kid1_str = kid1.build_bussproof_rec()
        the_str = kid1_str + r"\UnaryInfC" + r"{$" + token_str + "$}\n"

    return the_str

  def build_bussproof(self):
    the_str = self.build_bussproof_rec()

    return r"\begin{prooftree}" + "\n" + the_str + r"\end{prooftree}" + "\n"


  def draw_tree(self, verbose=False):
    draw_ast(self, verbose)

  # end of class Node

class Parser:
  AND_TOKEN = Token('and')

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
    # Check if self.current_token is of type token_types if token_types
    #   is a string, or belongs to token_types if token_types 
    #   is a tuple of strings.
    token = self.current_token
    if token is None:
      return False
    elif type(token_types) is not tuple: # must be a string in this case
        return token.token_type == token_types
    else:
      return token.token_type in token_types
    
  def check_token_value(self, token_values) -> bool:
    # Check if self.current_token is of value token_value.
    token = self.current_token
    if token is None:
      return False
    elif type(token_values) is not tuple: # must be a string in this case
      return token.value == token_values
    else:
      return token.value in token_values
    
  def parse(self) -> Node:
    # determine the type of self.tokens, whether it is a formula or a term
    is_formula = any([token.token_type in Token.FMLA_TOKENS 
                      for token in self.tokens])
    if is_formula:
      return self.formula() 
    else:
      return self.term()
  
  def formula(self) -> Node:
    node = self.comp_fmla1() # compound formula type 1

    while self.check_token_type('conn_arrow'): # 'imp', 'iff', 'xor'
      token = self.current_token
      if token is None:
        raise SyntaxError(f"Expected a token at {self.index}," +
                f" in expr(), but {self.current_token} is None.")
      self.advance()
      if token.value == 'imp':
        right_node = self.formula() # recursive call for right-assoc
      else:
        right_node = self.comp_fmla1() # left-assoc
      
      node = Node(token, [node, right_node]) 
    
    return node
    
  def comp_fmla1(self) -> Node:
    node = self.comp_fmla2() # compound formula type 2

    while self.check_token_type('conn_2ary'): # 'and', 'or'
      token = self.current_token
      self.advance()
      right_node = self.comp_fmla2()
      node = Node(token, [node, right_node]) # left-assoc

    return node

  def comp_fmla2(self) -> Node:
    if self.check_token_type('lparen'):
      self.advance()
      node = self.formula()
      if self.check_token_type('rparen'):
        self.advance()
      else:
        raise SyntaxError(f"Expected ')' at {self.index}," +
                f" in factor(), but {self.current_token} is given.")
    elif self.check_token_type(('conn_1ary','quantifier')): 
        # 'not' or 'forall' or 'exists'
      token = self.current_token 
      self.advance()
      right_node = self.comp_fmla2() # recursive call for right-assoc
      node = Node(token, [right_node])
    else:
      node = self.atom() # atomic formula (not identifier, the atomic term)

    return node
        
  def atom(self) -> Node:  # type: ignore # ignore Pylance error
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type(('conn_0ary', 'prop_letter')):
        # atomic formula case
        self.advance()
        return Node(token)
      elif self.check_token_type('pred_pre'): 
        # P(t1,t2,...) case
        self.advance()
        if self.check_token_type('lparen'):
          self.advance()
          args = []
          while True:
            args.append(self.term())
            if self.check_token_type('comma'):
              self.advance()
            elif self.check_token_type('rparen'):
              break
            else:
              raise SyntaxError(
                f"Expected ',' or ')' after predicate argument at " +
                f"{self.index} in atom(), but {self.current_token}" +
                f" is given.")
          # arity check
          if token.arity is None or token.arity != len(args):
            raise SyntaxError(
              f"Predicate {token.value} expects {token.arity} " +
              f"arguments, but {len(args)} were given")
          self.advance()
          return Node(token, args)
        else:
          raise SyntaxError(
            f"Expected '(' after predicate symbol at {self.index}" +
            f" in atom(), but {self.current_token} is given.")
      else:
        # t1 pred_in t2 case (such as t1 = t2, t1 < t2 etc.)
        # t1 = t2 < t3 ~ t4 is parsed as 
        #   (t1 = t2 and t2 < t3) and t3 ~ t4
        node = self.term()
        saved_node = None
        while self.check_token_type(('equality', 'pred_in')):
          token = self.current_token
          self.advance()
          right_node = self.term()
          if saved_node is None:
            node = Node(token, [node, right_node])
            saved_node = right_node
          else:
            new_node = Node(token, [saved_node, right_node])
            node = Node(self.AND_TOKEN, [node, new_node])
        return node
    else:
      raise SyntaxError("Unexpected end of input, in atom()")
      

  def term(self) -> Node:
    if self.check_token_value('-'):
      node = self.nterm1() 
    else:
      node = self.term1()

    while self.check_token_type('oper_in_1'):
      token = self.current_token
      self.advance()
      right_node = self.term1()
      node = Node(token, [node, right_node])
    return node
  
  def nterm1(self) -> Node:
    token = self.current_token
    if token is None or not self.check_token_value('-'):      
       node = self.term1()
    else:
      token.token_type = 'oper_pre'
      self.advance()
      unary_node = self.nterm1() # recursive call for right-assoc
      node = Node(token, [unary_node])

    return node
  
  def term1(self) -> Node:
    node = self.factor()
    while self.check_token_type('oper_in_2'):
      token = self.current_token
      self.advance()
      right_node = self.factor()
      node = Node(token, [node, right_node])

    return node

  def factor(self) -> Node:
    node = self.factor_exp()

    if self.check_token_type('oper_in_3'):
      token = self.current_token
      self.advance()
      right_node = self.factor() # recursive call for right-assoc
      node = Node(token, [node, right_node])

    return node
  
  def factor_exp(self) -> Node:
    node = self.factor_postfix()

    while self.check_token_type('oper_post'):
      token = self.current_token
      self.advance()
      node = Node(token, [node])

    return node
  
  def factor_postfix(self) -> Node:
    if self.check_token_type('lparen'):
      self.advance()
      node = self.term()
      if self.check_token_type('rparen'):
        self.advance()
      else:
        raise SyntaxError(
          f"Expected ')' after term at {self.index}," +
          f" in factor_postfix(), but {self.current_token} is given.")
    elif self.check_token_type('func_pre'):
      node = self.func_call()
    else:
      node = self.identifier()

    return node
  
  def func_call(self) -> Node:
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type('func_pre'):
        self.advance()
        if self.check_token_type('lparen'):
          self.advance()
          args = []
          while True:
            args.append(self.term())
            if self.check_token_type('comma'):
              self.advance()
            elif self.check_token_type('rparen'):
              break
            else:
              raise SyntaxError(
                f"Expected ',' or ')' after function argument at " +
                f"{self.index} in func_call(), but {self.current_token}" +
                f" is given.")
          # arity check
          if token.arity is None or token.arity != len(args):
            raise SyntaxError(
              f"Function {token.value} expects {token.arity} " +
              f"arguments, but {len(args)} were given")
          self.advance()
          return Node(token, args)  
        else:
          raise SyntaxError(
            f"Expected '(' after function symbol at {self.index}" +
            f" in func_call(), but {self.current_token} is given.")
      else:
        raise SyntaxError(f"Expected function symbol at {self.index} in" +
                          f" func_call(), but {token} is given.")
    else:
      raise SyntaxError("Unexpected end of input, in func_call()")

  def identifier(self) -> Node:
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type(('const', 'numeral', 'var')):
        self.advance()
        return Node(token)
      else:
        raise SyntaxError(f"Expected identifier at {self.index} in" +
                          f" identifier(), but {token} is given.")
    else:
      raise SyntaxError("Unexpected end of input, in identifier()")

def parse_text(input_text):
  tokens = tokenizer(input_text)
  parser = Parser(tokens)
  ast = parser.parse() # ast = Abstract Syntax Tree
  if parser.current_token is not None:
    raise SyntaxError(
      f"Unexpected token '{parser.current_token}' at {parser.index}," +
      f" in parse_text(), while end of input expected.")
  return ast

#region (3/3) Utils for rendering AST ## ------------------------------

def build_GNode(ast, xpos, ypos, ax, r):
  LATEX_DICT = Node.LATEX_DICT
  
  # post-order traversal (unlike the other 3 methods)
  if(ast.children):
    children = [build_GNode(kid, xpos, ypos, ax, r) 
                for kid in ast.children]
  else:
    children = []
  label = ast.token.value

  if ast.token.token_type == 'prop_letter':
    label = Node.ident2latex(ast.token)
  else:
    label = LATEX_DICT[label]
  
  txt = ax.text(xpos, ypos, '$' + label + '$', 
                ha='center', va='center', fontsize=6, alpha=0)
  return GNode(txt, ax, r, children=children)

def draw_ast(ast, verbose=False):
  import matplotlib.pyplot as plt

  plt.rcParams["mathtext.fontset"] = "cm" 
    # cm = computer modern by Donald Knuth
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

#endregion

#region (4/4) Draw bussproof style Trees ## ---------------------------

class Tbox: # text object together with its position and size
  def __init__(self, txt, ax, r):
    # txt is a text object
    # r is a renderer
    self.txt = txt # matplotlib.text.Text object
      # txt.get_text() is the label (latex source string)
    bbox = txt.get_window_extent(renderer=r) # unit: pixel
    bbox_d = bbox.transformed(ax.transData.inverted()) 
      # unit: data coordinate
    x, y = txt.get_position()
    self.x = x
    self.y = y
    self.width = bbox_d.width
    self.height = bbox_d.height

  def __str__(self):
    return (f"x = {self.x:.3f}, y = {self.y:.3f}, " + 
            f"w = {self.width:.3f}, h = {self.height:.3f}")
    
class GNode: # graph node
  def __init__(self, txt, ax, r, unit_len = 0.12, kx=3, ky=1, 
               overhang=0.14, children=None):
    # txt = ax.text(pos_x, pos_y, string, ..) is a text object
    # r is a renderer
    # dx is the horizontal distances between the children
    # dy is the vertical distance between the root and the children    
    # children is a list of Node objects    
    # Root's position is (0, 0). When rendering, we will shift the
    # node's center to the center of the figure.
    # The root and each child's position is relative to the center
    # of the node.
    
    self.parent = None # This changes later iff 
                       # self is not the real(one and only) root.
    self.x = self.y = 0
    self.root = tbox = Tbox(txt, ax, r)
    self.children = None
    self.unit_height = unit_len
    self.overhang = overhang
    # Both (self.x, self.y) and (self.root.x, self.root.y) are 
    # positions of the root of self.  
    # The meaning of (self.x, self.y) depends on self.parent.
    # If self.parent is None, then (self.x, self.y) is not used at all.
    # If self.parent is not None, then (self.x, self.y) is the position 
    # of the root of self relative to the root of self.parent.
    # (self.root.x, self.root.y) has meaning iff self.parent is None.
    # It is the position (x, y) given when the text object was created
    # by ax.text(x, y, ...) 
    # Normally it is (center_x, center_y) of the axis.

    dx = kx * unit_len
    dy = ky * unit_len
    unit_height = self.unit_height 
      # height of each node (considered as a rectangle)
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
      # dlrkids = distance between the leftmost kid's root and the 
      # rightmost kid's root
      #    = tot_width - (children[0].width + children[-1].width)/2
      # xvec = [-dlrkids/2, += children[0].width/2 + 
      #   children[1].width/2 + dx, += ...]
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
          kid.x = children[i-1].x + children[i-1].width/2 + dx + \
                  children[i].width/2
      
      assert abs(children[-1].x - dlrkids/2) < 1e-6, \
             "the last child's x is wrong"

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
      x_ref, y_ref = (self.root.x, self.root.y) 
        # normally (center_x, center_y)
      if self.children: 
          # Then we shift the root down and maybe left/right too
          # so that the center of the whole tree coincides with 
          # the center of the axis.
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
                    x+node_right.x+self.overhang, linewidth=0.2, 
                    color='black')
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
                   self.x + node_left.x - self.overhang, 
                   self.x + node_right.x + self.overhang,
                   linewidth=0.2, color='black')
      # draw subtrees
      for kid in self.children:
        kid.draw_tree(plt1)
# endregion
