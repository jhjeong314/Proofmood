from typing import List

from first_order_logic_parse import *

class Formula:
  def __init__(self, input: str | Node):
    try:
      if isinstance(input, str):
        self.ast = parse_text(input) 
      else:
        self.ast = input
      if self.ast.type == 'term':
        str1 = (str if isinstance(input, str) 
          else input.build_infix('text'))
        print(f"Input \"{str1}\" is a term, not a formula.")
    except ValueError as e:
      print(f"ValueError: {e}")
    except SyntaxError as e:
      print(f"SyntaxError: {e}")

  def __str__(self):
    return self.ast.build_infix('text')
  
  def __eq__(self, other):
    infix_self = self.ast.build_infix('text')
    infix_other = other.ast.build_infix('text')
    return infix_self == infix_other
  
  def display_infix(self, opt: str='latex'):
    from IPython.display import display, Math
    s = self.ast.build_infix(opt)
    if opt == 'latex':
      display(Math(f"${s}$")) 
    else:
      print(s)

  def subformula_at(self, pos: List[int]):
    if pos == []:
      return self
    else:
      ast = self.ast
      for i in pos:
        ast = ast.children[i]
      return Formula(ast)
    
  def get_prime_subformulas(self) -> set:
    prime_subs = set()
    tree = self.ast
    if tree.token.token_type in Token.NON_PRIME_FMLA:
      for kid in tree.children:
        prime_subs |= Formula(kid).get_prime_subformulas()
    else:
      prime_subs |= { self.ast.build_infix('text') }
    return prime_subs

  def get_truth_tree(self, prime_subs_li: List[str]) -> None:
    # In List[str], str is the infix notation of a formula.
    # Each node in a truth tree is assigned the value i where i is the 
    # index of the formula at node in prime_subs_li.
    # Other than this, truth tree is the same as node.
    # prime_subs_li is a list of prime subformulas of some formulas,
    # probably including self.
    def rec_fn(ast: Node) -> None:
      if ast.token.token_type in Token.NON_PRIME_FMLA:
        for ast_i in ast.children:
          rec_fn(ast_i)
      else:
        ast.index = prime_subs_li.index(ast.build_infix('text'))

    rec_fn(self.ast)
  
  def eval_truth_tree(self, tVal_assign: str) -> None:
    # tVal_assign is a truth-value assignment represented by a string of
    # 0's and 1's. The length of tVal_assign is the number of propositional
    # letters in the formula(s).
    # This method is called after get_truth_tree() is called.
    # To build a truth table, this method is called 2^n times, where n is
    # the number of propositional letters in the formula(s).
    # Note that get_truth_tree() is called only once.
    def rec_fn(ast: Node) -> None:
      if ast.token.token_type in Token.NON_PRIME_FMLA:
        # do the job for the children of the node first
        for ast_i in ast.children:
          rec_fn(ast_i)
        # then do the job for the node itself
        token_value = ast.token.value
        if token_value == 'not':
          ast.bValue = 1 - ast.children[0].bValue
        elif token_value == 'and':
          ast.bValue = min(ast.children[0].bValue, ast.children[1].bValue)
        elif token_value == 'or':
          ast.bValue = max(ast.children[0].bValue, ast.children[1].bValue)
        elif token_value == 'imp':
          ast.bValue = max(1 - ast.children[0].bValue, 
                           ast.children[1].bValue)
        elif token_value == 'iff':
          ast.bValue = 1 - abs(ast.children[0].bValue - 
                               ast.children[1].bValue)
        elif token_value == 'xor':
          ast.bValue = abs(ast.children[0].bValue - 
                           ast.children[1].bValue)
        else:
          print(f"Error: unknown connective \"{token_value}\".")
      else:
        if ast.index >= 0:
          ast.bValue = int(tVal_assign[ast.index])
        else: # ast.index == -1 which means ast is bot, 
              #   the constant False.
          ast.bValue = 0

    rec_fn(self.ast)

  def get_bValues(self) -> List[int]:
    # This method is called after eval_truth_tree() is called
    # for a specific truth-value assignment.
    # The order of elements of bValues: List[int] follows that of
    # the polish notation of the formula.
    def rec_fn(ast: Node) -> List[int]:
      bValues = []
      bValues.append(ast.bValue)
      if ast.token.token_type in Token.NON_PRIME_FMLA:
        bValues_add = []
        for ast_i in ast.children:
          bValues_i = rec_fn(ast_i)
          bValues_add.extend(bValues_i)
        bValues.extend(bValues_add)
      return bValues
    return rec_fn(self.ast)

FList = List[Formula]

class Truth_table:
  def  __init__(self, f_list: FList):
    self.f_list = f_list

  def get_prime_subformulas(self) -> set:
    prime_subs = set()
    for f in self.f_list:
      prime_subs |= f.get_prime_subformulas()
    return prime_subs

  @staticmethod
  def get_binary(n: int, len: int) -> str:
    # n is an integer in the range [0, 2^len - 1]
    # len is the number of propositional letters in the formula(s)
    # E.g., if n=5, len=4, then return '0101'.
    return bin(n)[2:].zfill(len)
  
  # def truth_tree(self) -> Node:
  #   prime_subs_li = sorted(list(self.get_prime_subformulas()))
  #   n = len(prime_subs_li) # number of propositional letters

  #   ast = self.ast
  #   return ast
