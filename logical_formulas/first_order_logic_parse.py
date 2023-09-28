# This file is imported by first_order_logic_parser.ipynb.

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
  OPER_IN_2N = [ "/", "%", "div" ]
  OPER_IN_3 = [ "^" ]
  PRED_IN = [ "!=", "<", "<=", ">", ">=", "nless", "nleq", "ngtr", "ngeq",
              "divides", "in", "nin", "subseteq",
              "nsubseteq", "subsetneqq", "supseteq", "nsupseteq",
              "supsetneqq", "divides", "ndivides", "sim", "simeq",
              "cong", "equiv", "approx" ]
  RESERVED_WORDS = set(CONSTS + OPER_PRE + OPER_POST + OPER_IN_1 + 
                      OPER_IN_2 + OPER_IN_3 + PRED_IN)
  SPECIAL_CHARS = "-!'^#+*/%=<>()[]{},"
  FMLA_TOKENS = ("pred_pre", "pred_in", "equality", "prop_letter", 
    'conn_0ary') 
    # an expression is a formula iff it has a token in FMLA_TOKENS
  FMLA_ROOTS = FMLA_TOKENS + ("conn_1ary", "conn_2ary", "conn_arrow", 
    "quantifier", "var_determiner") 
    # a parsed node is a formula iff it has a token in FMLA_ROOTS
  NON_PRIME_ROOTS = ("conn_1ary", "conn_2ary", "conn_arrow")
  PRIME_ROOTS = ("pred_pre", "pred_in", "equality", "prop_letter",
    "quantifier", "conn_0ary")

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
      self.arity = 2
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
    elif value in OPER_PRE: # this won't be used
      # 'oper_pre' type is set in the parser
      self.token_type = 'oper_pre' # unary '-', ..
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
        self.precedence = 9
      elif value[0] in "uvw" + "xyz" + "ijk" + "lmn":
        # we use concatenation to avoid the stupid cSpell warning
        if (len_s==1 or 
            (len_s >= 3 and value[1]=='_' 
             and Token.isword(value[2:], "decimal"))):
          self.token_type = 'var'
          self.precedence = 9
        else:
          raise ValueError(f"'{value}' is invalid variable symbol (Token)")
      elif value[0] in "abcde" :
        if len_s==1 or Token.isword(value[1:]):
          self.token_type = 'const'
          self.precedence = 9
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
    # test if s is the string for a non-negative integer
    return s.isdecimal() and (len(s) == 1 or s[0]!='0')
  
  @staticmethod
  def is_nat(s: str) -> bool:
    # test if s is the string for a positive integer
    return s.isascii() and s.isdecimal() and s[0]!='0'
  
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
      raise ValueError("tokenizer(): " 
                       f"'{s}' is invalid (illegal character)")
    
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

#region Comment
# <formula> ::= { <comp_fmla1> "imp" } <comp_fmla1> | 
#                 <comp_fmla1> { ( "iff" | "xor") <comp_fmla1> }
# <comp_fmla1> ::= <comp_fmla2> { ("and" | "or") <comp_fmla2> }
# <comp_fmla2> ::= { ("not" | <determiner>) } 
#                  ( '(' <formula> ')' | <atom> | "bot" )
# <determiner> ::= <quantifier> <var>
# <quantifier> ::= "forall" | "exists"
# <atom> ::= <prop_letter> | <pred_pre> "(" <term> {',' <term>} ")" |
#            <term> <pred_in> <term>
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
  from typing import List

  def __init__(self, token, children=None):
    self.token = token # the node is labeled with a Token object
    self.children = children if children else [] 
    #^ list of Node objects (not list of Token objects)
    self.type = ('formula' if self.token.token_type in Token.FMLA_ROOTS 
                           else 'term')
    self.index = -1 # 0,1,2,.. for truth tree
    self.bValue = -1 # 0,1 for truth tree
    self.level = -1 # 0,1,2,.. for truth tree
    self.alt_str = '' # P_1, P_1, .. for truth tree

  def __str__(self):
    return self.build_polish_notation()

  def __eq__(self, other):
    # return infix_self == infix_other
    return f"{self}" == f"{other}"
  
  def longer_than(self, other):
    """ Test whether the infix string of self is longer than that of other.
      This method is used as a pretest for whether self is a subformula of 
      other. """
    infix_self = self.build_infix('text')
    infix_other = other.build_infix('text')
    return len(infix_self) > len(infix_other)

  LATEX_DICT = dict(
      [("not", r"\neg"), ("and", r"\wedge"), ("or", r"\vee"),
      ("imp", r"\rightarrow"), ("iff", r"\leftrightarrow"),
      ("xor", r"\nleftrightarrow"), ("nin", r"\not\in"), ("bot", r"\bot"), 
      ("emptyset", r"\varnothing"), ("^o", r"^{\circ}"), ("^inv", r"^{-1}"), 
      ("^#", r"^\#"), ("%", r"\%"), ("<=", r"\le"), (">=", r"\ge"), 
      ("divides", r"\,\vert\,"), ("ndivides", r"\;\vert\mskip-14mu\not\;\;"),
      ("forall", r"\forall"), ("exists", r"\exists")])
    #region Comment
    # Other than the above and '^', for all reserved tokens, just use 
    # ("token.value", r"\token.value") for the mapping.
    # Special care is needed for '^'. See the build_infix_formula() 
    #   method below.
    # For user-defined tokens, use the static method ident2latex(opt).
    #endregion

  @staticmethod
  def token2latex(token: Token, opt: str='latex') -> str:
    # for oper_*, pred_in (declared in Token class)
    label = token.value
    if opt == 'latex':
      if (latex_str := Node.LATEX_DICT.get(label)):
        return latex_str
      elif label.isalnum():
          return f"\\{label}"
      else:
        return label
    else: # opt == 'text'
      return label
    
  @staticmethod
  def ident2latex(token: Token, opt: str='latex') -> str:
    #region Comment
    # for const, var, func_pre, pred_pre, prop_letter, numeral
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
    if opt == 'latex':
      pos_underscore = label.rfind('_')
      if (label[-1].isdecimal() and 
          token.token_type in ("func_pre", "pred_pre") and
          (pos_underscore < 0 or pos_underscore != len(label)-2)):
        label = label[:-1] # chop-off the last character
      
      if pos_underscore >= 0: # underscore exists in the identifier
        str1 = label[:pos_underscore]
        str2 = label[pos_underscore+1:]
        subscript = r"_{" + str2 + r"}" if str2 else ""
      else:
        str1 = label
        subscript = ""

      if len(str1) > 1 and not str1.isdecimal():
        left_str = r"{\rm " + str1.replace("_", r"\_") + r"}"
      else: 
          left_str = str1

      return left_str + subscript
    else: # opt == 'text'
      return label

  @staticmethod
  def display_latex_li(str_li: List[str]) -> None:
    from IPython.display import display, Math
    node_li = [parse_ast(s) for s in str_li]
    latex_str_li = [node.build_infix('latex') for node in node_li]
    latex_str = ',\\: '.join(latex_str_li)
    display(Math('$[\\,' + latex_str + '\\,]$'))

  def build_polish_notation(self, verbose=False) -> str:
    ret_str = f"{self.token}" if verbose else f"{self.token.value}"
    if self.children:
      ret_str += ' '
      ret_str += ' '.join(child.build_polish_notation(verbose) 
                        for child in self.children)
    return ret_str
  
  def build_RPN(self, verbose=False) -> str:
    ret_str = ''
    if self.children:
      ret_str += ' '.join(child.build_RPN(verbose) 
                          for child in self.children) + ' '
      
    ret_str += f"{self.token}" if verbose else f"{self.token.value}"
    
    return ret_str

  def build_infix(self, opt: str='latex') -> str:
    if self.type == 'term':
      return self.build_infix_term(opt)
    else: # self.type == 'formula'
      return self.build_infix_formula(opt)
            
  def build_infix_term(self, opt: str) -> str:
    LATEX_DICT = self.LATEX_DICT
    if not self.children: # leaf node ::= variable | const | numeral
      return self.ident2latex(self.token, opt)
    else: # non-leaf node
      # token_type ::= func_pre | oper_in_1 | oper_in_2 | oper_in_3 |
      #                oper_pre | oper_post 
      ret_str = ''
      if self.token.token_type == 'func_pre':
        label = self.ident2latex(self.token, opt)
        args = ', '.join(kid.build_infix(opt) for kid in self.children)
        ret_str += label + '(' + args + ')'
      else: # token is an operator with various arities and precedences
        if self.token.precedence == 1: 
          # oper_pre(unary) or oper_in_1(binary, +, -, cap, cup, oplus)
          if self.token.token_type == 'oper_pre':
            kid1 = self.children[0]
            kid1_str = kid1.build_infix(opt)
            if kid1.token.precedence == 1:
              kid1_str = '(' + kid1_str + ')'
            # else pass
            ret_str += self.token2latex(self.token, opt) + kid1_str
          else: # oper_in_1
            kid1, kid2 = self.children
            kid1_str = kid1.build_infix(opt)
            kid2_str = kid2.build_infix(opt)
            if ((self.token.value in Token.OPER_PRE and kid2.token.precedence == 1) or
                kid2.token.token_type == 'oper_pre'):
              kid2_str = '(' + kid2_str + ')'
            # else pass
            ret_str += kid1_str + ' ' + self.token2latex(self.token, opt) + ' ' + kid2_str
        elif self.token.precedence == 2: # oper_in_2(binary, *, /, %, ...)
          kid1, kid2 = self.children
          kid1_str = kid1.build_infix(opt)
          kid2_str = kid2.build_infix(opt)
          # determine if parentheses are needed
          if (kid2.token.precedence < self.token.precedence or
              # '/', '%', 'div' are non-associative
              (kid2.token.precedence == self.token.precedence and 
               self.token.value in Token.OPER_IN_2N)): 
            kid2_str = '(' + kid2_str + ')'
          if kid1.token.precedence < self.token.precedence:
            kid1_str = '(' + kid1_str + ')'
          ret_str += kid1_str + ' ' + self.token2latex(self.token, opt) + \
                     ' ' + kid2_str
        elif self.token.precedence == 3: # oper_in_3(binary, ^ exponentiation)
          kid1, kid2 = self.children
          kid1_str = kid1.build_infix(opt)
          kid2_str = kid2.build_infix(opt)
          # determine if parentheses are needed
          if kid1.token.precedence <= 4:
            # '^' is right-associative, and we want parentheses in (a')^2
            kid1_str = '(' + kid1_str + ')'
          if kid2.token.precedence < self.token.precedence:
            pass # In a^(b+c), we don't need parentheses around b+c
                 # when it is LaTeXed. 
          ret_str += kid1_str + '^' + '{' + kid2_str + '}'
        else: # precedence = 4. Must be of type OPER_POST.
          kid1 = self.children[0]
          kid1_str = kid1.build_infix(opt)
          if kid1.token.precedence <= self.token.precedence: 
            # true unless kid1 is an atomic term
            kid1_str = '(' + kid1_str + ')'
          ret_str += kid1_str + self.token2latex(self.token, opt)
      return ret_str

  def build_infix_formula(self, opt: str='text') -> str:  
    LATEX_DICT = self.LATEX_DICT

    # 1. atomic formulas and bot
    if not self.children: # 'prop_letter' or 'conn_0ary'
      # 1.1 terminal nodes
      if self.token.token_type == 'prop_letter':
        return self.ident2latex(self.token, opt)
      else: # self.token.value must be 'bot'
        return (LATEX_DICT[self.token.value] if opt=='latex' 
                else self.token.value)
    elif self.token.token_type in Token.FMLA_TOKENS: 
      # 'pred_pre', 'pred_in', 'equality'
      # 1.2 internal nodes
      if self.token.token_type == 'pred_pre': # prefix predicate
        label = self.ident2latex(self.token, opt)
        args = ', '.join(kid.build_infix(opt) for kid in self.children)
        return label + '(' + args + ')'
      else: # 'pred_in' or 'equality' # infix predicate
        kid1, kid2 = self.children
        kid1_str = kid1.build_infix(opt)
        kid2_str = kid2.build_infix(opt)
        return (kid1_str + ' ' + self.token2latex(self.token, opt) + 
                ' ' + kid2_str)
    # 2. compound formulas except bot -- i.e., connectives 
    #    and quantifiers
    else: 
      ret_str = ''
      if self.token.arity == 2:
        # 2.1 binary connectives
        token_str = (' ' + LATEX_DICT[self.token.value] + ' '
                     if opt=='latex' else f" {self.token.value} ")
        kid1, kid2 = self.children
        kid1_str = kid1.build_infix(opt)
        kid2_str = kid2.build_infix(opt)
        if self.token.token_type == 'conn_arrow': # 'imp', 'iff', 'xor'
          # determine whether we need parentheses around kid1
          if kid1.token.token_type == 'conn_arrow':
            if self.token.value != kid1.token.value:
              kid1_str = f"({kid1_str})"
            else:
              if self.token.value == "imp":
                kid1_str = f"({kid1_str})"
              else:
                pass # iff and xor are associative
          # determine whether we need parentheses around kid2
          if kid2.token.token_type == 'conn_arrow':
            if self.token.value != kid2.token.value:
              kid2_str = f"({kid2_str})"
            else:
              pass # even 'imp' is right-associative
        else: # 'and', 'or' (precedence == 2)
          # determine whether we need parentheses around kid1
          if kid1.token.token_type == 'conn_arrow':
            kid1_str = f"({kid1_str})"
          elif (kid1.token.token_type == 'conn_2ary' and 
                self.token.value != kid1.token.value):
            kid1_str = f"({kid1_str})"
          # determine whether we need parentheses around kid2
          if kid2.token.token_type == 'conn_arrow':
            kid2_str = f"({kid2_str})"
          elif (kid2.token.token_type == 'conn_2ary' and
                self.token.value != kid2.token.value):
              kid2_str = f"({kid2_str})"
          # x < y = z case
          if self.token.value == 'and':
            if (v_str := self.seq_infix(opt)):
              return v_str 
            else:
              pass
        ret_str += kid1_str + token_str + kid2_str
      elif self.token.token_type == 'conn_1ary': 
        # 2.2 unary connectives (actually, negation only)
        # 'not bot' case. This is a special case because we don't want
        #   to render it as '\neg \bot'. This corresponds 
        #   to the **empty formula**, which is interpreted as True.
        if self.token.value == 'not' and \
          self.children[0].token.value == 'bot':
          return ''
        token_str = (LATEX_DICT[self.token.value] + r'\, ' if opt=='latex'
                     else self.token.value + ' ')
        kid1 = self.children[0]
        kid1_str = kid1.build_infix(opt)
        # determine whether we need parentheses around kid1
        if kid1.token.token_type in ('conn_2ary', 'conn_arrow', 'pred_in', 'equality'):
          kid1_str = f"({kid1_str})"
        ret_str += token_str + kid1_str
      else:
         # 2.3 quantifier
        token_str = (LATEX_DICT[self.token.value] if opt=='latex'
                     else self.token.value) + ' '
        kid1 = self.children[0] # a variable for determiner
        kid1_str = self.ident2latex(kid1.token, opt)
        kid11 = kid1.children[0]
        kid11_str = kid11.build_infix(opt)
        # determine whether we need parentheses around kid11
        if kid11.token.token_type in ('pred_in', 'equality'):
          kid11_str = f"({kid11_str})"
        ret_str += (token_str + kid1_str + (r"\, " if opt=='latex' else " ") + 
                    kid11_str)
      return ret_str  

  def seq_infix(self, opt) -> str:
    # sequence of terms connected by infix operators: i.e., x < y = z, which
    #   is parsed as x < y and y = z.
    # This method is called iff self.token.value == 'and'.
    kid1, kid2 = self.children
    if kid2.token.token_type in ('pred_in', 'equality'):
      if kid1.token.token_type in ('pred_in', 'equality'):
        if kid1.children[1] == kid2.children[0]:
          kid1_str = kid1.build_infix(opt)
          kid2_token_str = kid2.token2latex(kid2.token, opt)
          kid22_str = kid2.children[1].build_infix(opt)
          return ' '.join([kid1_str, kid2_token_str, kid22_str])
        else:
          return ''
      elif kid1.token.value == 'and':
        if (kid1.children[1].children[1] == kid2.children[0] and
            (kid1_str := kid1.seq_infix(opt))):
          kid2_token_str = kid2.token2latex(kid2.token, opt)
          kid22_str = kid2.children[1].build_infix(opt)
          return ' '.join([kid1_str, kid2_token_str, kid22_str])
        else:
          return ''
      else:
        return ''
    else:
      return ''

  def display_infix(self, opt: str='latex'):
    from IPython.display import display, Math
    s = self.build_infix(opt)
    if opt == 'latex':
      display(Math(f"${s}$")) 
    else:
      print(s)

  #region comment
  # bussproof tree has the following structure:
  # 1. terminal node: \AxiomC{..}
  #    terms, prop letters, and bot
  # 2. non-terminal node: \UnaryInfC{..}, \BinaryInfC{..}, \TrinaryInfC{..}
  #    predicate symbol(prefix and infix), equality
  #      prefix predicate's arity is at most 3
  #    connectives(unary and binary)
  #    quantifier + var_determiner
  #endregion
  def build_bussproof(self): # wrapper of build_bussproof_rec()
    the_str = self.build_bussproof_rec()
    return r"\begin{prooftree}" + "\n" + the_str + r"\end{prooftree}" + "\n"

  def build_bussproof_rec(self):
    LATEX_DICT = self.LATEX_DICT

    if self.type == 'term':
      # terminal node. use \AxiomC{..}
      label = self.build_infix_term('latex')
      the_str = r"\AxiomC" + r"{$" + label + "$}\n"
    # self.type == 'formula'
    elif not self.children: 
      # terminal node. use \AxiomC{..}
      if self.token.token_type == 'prop_letter':
        label = self.ident2latex(self.token)
      else: # self.token.value must be 'bot'
        label = LATEX_DICT[self.token.value]
      the_str = r"\AxiomC" + r"{$" + label + "$}\n"
    else: # pred_pre, pred_in, equality, 
          # conn_1ary, conn_2ary, conn_arrow, quantifier
      label = (self.ident2latex(self.token) 
               if self.token.token_type == 'pred_pre' 
               else self.token2latex(self.token))
      arity = self.token.arity # must be 1, 2, or 3
      if arity == 1: # not, forall, exists, unary predicate
        if self.token.token_type in ('conn_1ary', 'pred_pre'):
          kid1 = self.children[0]
          kid1_str = kid1.build_bussproof_rec()
          the_str = kid1_str + r"\UnaryInfC" + r"{$" + label + "$}\n"
        else: # quantifier
          kid1 = self.children[0] # a variable for determiner
          kid1_str = self.ident2latex(kid1.token)
          kid11 = kid1.children[0]
          kid11_str = kid11.build_bussproof_rec()
          the_str = (kid11_str + r"\UnaryInfC" + r"{$" + label + ' ' +
                     kid1_str + "$}\n")
      elif arity == 2:
        kid1, kid2 = self.children
        kid1_str = kid1.build_bussproof_rec()
        kid2_str = kid2.build_bussproof_rec()
        the_str = (kid1_str + kid2_str + r"\BinaryInfC" + r"{$" +
                    label + "$}\n")
      elif arity == 3:
        kid1, kid2, kid3 = self.children
        kid1_str = kid1.build_bussproof_rec()
        kid2_str = kid2.build_bussproof_rec()
        kid3_str = kid3.build_bussproof_rec()
        the_str = (kid1_str + kid2_str + kid3_str + r"\TrinaryInfC" + r"{$" +
                    label + "$}\n")
      else:
        raise ValueError(f"arity of predicate symbol cannot be {arity}")

    return the_str

  def draw_tree(self, verbose=False):
    try:
      from draw_tree import draw_ast
    except ImportError: 
      url = 'https://raw.githubusercontent.com/jhjeong314/Proofmood/main/logical_formulas'
      import httpimport
      with httpimport.remote_repo(url):
        # for Google Colab, which has limited capabilities with LaTeX
        from draw_tree1 import draw_ast 
    draw_ast(self, verbose)

  #region syntactic manipulations
  def node_at(self, pos: List[int]):
    # The return value may be a term or a formula.
    if pos == []:
      return self
    else:
      ast = self
      for i in pos:
        ast = ast.children[i]
      return ast
    
  def replace_node_at(self, pos: List[int], new_node, 
                      dupl: str = ''):
    # Make sure to replace subformula by a formula and
    # a subterm by a term.
    # dupl is either '' or 'dupl'. In the 1st case, We update self 
    # and return None.  In the 2nd case, we create a new node by 
    # the replacement and return the new node.
    # pos must be nonempty.
    import copy

    assert isinstance(new_node, Node), \
      "Node.replace_node_at(): new_node must be a Node object"
    # I had to type check in this way. 
    # type hinting "new_node: Node" does not work.

    node0 = self if dupl == '' else copy.deepcopy(self)
    node = node0
    for i in pos[:-1]:
      assert len(node.children) > i, \
        "Node.replace_node_at(): pos is out of range"
      node = node.children[i]
    node.children[pos[-1]] = copy.deepcopy(new_node)
    if dupl == 'dupl':
      return node0

  def replace_nodes_at(self, pos_li: List[List[int]],
                      new_node_li, dupl: str=''):
    # This method is a multiple version of replace_node_at().
    # Members of pos_li must be incomparable.
    import copy

    assert len(pos_li) == len(new_node_li)
    if dupl != 'dupl':
      for i in range(len(pos_li)):
        self.replace_node_at(pos_li[i], new_node_li[i])
    else: 
      node0 = copy.deepcopy(self)
      for i in range(len(pos_li)):
        node0.replace_node_at(pos_li[i], new_node_li[i])
      return node0  

  def substitute(self, var: str, new_node, dupl: str = ''):
    # Input argument var is a string, which can be either an individual 
    # variable/constant or a propositional variable.
    # There is no difference in the code for handling these two cases.
    import copy

    node = copy.deepcopy(self) if dupl == 'dupl' else self
    if node.token.value == var:
      node = copy.deepcopy(new_node)
    elif node.children:
      for i, kid in enumerate(node.children):
        # note that dupl=='dupl' is passed to the recursive call
        node.children[i] = kid.substitute(var, new_node, 'dupl')
    
    if dupl == 'dupl':
      return node

  #endregion syntactic manipulations

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
        raise SyntaxError("Parser.expr(): Expected a token at " 
          f"{self.index}, encountered None.")
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
        raise SyntaxError("Parser.comp_fmla2(): Expected ')' at " 
          f"{self.index}, but encountered {self.current_token}.")
    elif self.check_token_type('conn_0ary'):
      token = self.current_token
      self.advance()
      node = Node(token)
    elif self.check_token_type('conn_1ary'): # 'not' 
      token = self.current_token 
      self.advance()
      right_node = self.comp_fmla2() # recursive call for right-assoc
      node = Node(token, [right_node])
    elif self.check_token_type('quantifier'):
      token_q = self.current_token
      self.advance()
      token_v = self.current_token
      if token_v is None or token_v.token_type != 'var':
        raise SyntaxError("Parser.comp_fmla2(): Expected a variable at "
          f"{self.index}, but encountered {self.current_token}.")
      token_v.token_type = 'var_determiner'
      token_v.arity = 1
      self.advance()
      right_node = self.comp_fmla2() # recursive call for right-assoc
      node = Node(token_q, [Node(token_v, [right_node])])
    else:
      # atomic formula (not identifier or equivalently, not the atomic term)
      # formulas like a < b = c are considered as atomic formulas
      node = self.atom() 

    return node
        
  def atom(self) -> Node:  # type: ignore # ignore Pylance error
    # formulas like a < b = c are considered as atomic formulas
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type('prop_letter'):
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
              raise SyntaxError("Parser.atom(): Expected ',' or ')' after "
                f"predicate argument at {self.index},\n" 
                f" but encountered {self.current_token}")
                
          # arity check
          if token.arity is None or token.arity != len(args):
            raise SyntaxError(f"Parser.atom(): Predicate {token.value} "
              f"expects {token.arity} arguments, but " 
              f"{len(args)} arguments are given.")
          self.advance()
          return Node(token, args)
        else:
          raise SyntaxError(f"Parser.atom(): Expected '(' after predicate "
            f"symbol at {self.index}, but encountered {self.current_token}.")
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
          else:
            new_node = Node(token, [saved_node, right_node])
            node = Node(self.AND_TOKEN, [node, new_node])
          saved_node = right_node
        return node
    else:
      raise SyntaxError("Parser.atom(): Unexpected end of input")
      

  def term(self) -> Node:
    if self.current_token and \
       self.current_token.value in Token.OPER_PRE:
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
    if token is None or \
       not (self.current_token and \
            self.current_token.value in Token.OPER_PRE):      
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
        raise SyntaxError("Parser.factor_postfix(): Expected ')' at "
          f"{self.index}, but encountered {self.current_token}.")
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
              raise SyntaxError("Parser.func_call(): "
                f"Expected ',' or ')' after function argument \n\tat " +
                f"{self.index}, but encountered {self.current_token}.")
          # arity check
          if token.arity is None or token.arity != len(args):
            raise SyntaxError("Parser.func_call(): "
              f"Function {token.value} expects \n\t{token.arity} " +
              f"arguments, but {len(args)} arguments are given")
          self.advance()
          return Node(token, args)  
        else:
          raise SyntaxError("Parser.func_call(): "
            f"Expected '(' after function symbol \n\tat {self.index}," +
            f" but encountered {self.current_token}.")
      else:
        raise SyntaxError("Parser.func_call(): Expected function "
          f"symbol at {self.index} but encountered {token}.")
    else:
      raise SyntaxError("Parser.func_call(): Unexpected end of input")

  def identifier(self) -> Node:
    if self.current_token is not None:
      token = self.current_token
      if self.check_token_type(('const', 'numeral', 'var')):
        self.advance()
        return Node(token)
      else:
        raise SyntaxError("Parser.identifier(): Expected an identifier"
          f" at {self.index},\n\tbut encountered {token}.")
    else:
      raise SyntaxError("Parser.identifier(): Unexpected end of input")

def parse_ast(input_text):
  tokens = tokenizer(input_text)
  parser = Parser(tokens)
  ast = parser.parse() # ast = Abstract Syntax Tree
  if parser.current_token is not None:
    raise SyntaxError("parse_ast(): "
      f"Unexpected token '{parser.current_token}' \n"
      f"\tat {parser.index}, while end of input expected.")
  return ast

