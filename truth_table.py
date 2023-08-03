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
        str_infix = (str if isinstance(input, str) 
          else input.build_infix('text'))
        print(f"Input \"{str_infix}\" is a term, not a formula.")
    except ValueError as e:
      print(f"ValueError: {e}")
    except SyntaxError as e:
      print(f"SyntaxError: {e}")

  def __str__(self):
    return self.ast.build_infix('text')
  
  def __eq__(self, other) -> bool:
    return self.ast == other.ast
  
  def display_infix(self, opt: str='latex'):
    import copy

    if opt != 'truth_table':
      self.ast.display_infix(opt) # 'latex' or 'text'
    else:
      new_ast = copy.deepcopy(self.ast)
      def rec_fn(node: Node) -> None:
        if node.token.token_type in Token.NON_PRIME_ROOTS:
          for kid in node.children:
            rec_fn(kid)
        elif node.token.token_type != 'conn_0ary': 
          # node must be prime subformula
          node.children = None
          if node.index >= 0:
            if node.alt_str.startswith('P_'):
              node.token.value = f"P{node.alt_str[2:]}"
            else:
              node.token.value = f"{node.alt_str}"
          else:
            node.token.value = 'bot'
      rec_fn(new_ast)
      new_fmla = Formula(new_ast)
      new_fmla.ast.display_infix('text')

  def node_at(self, pos: List[int]) -> Node:
    return self.ast.node_at(pos)
  
  def replace_node_at(self, pos: List[int], new_node: Node, 
                      dupl: str = ''):
    node = self.ast.replace_node_at(pos, new_node, dupl)
    if dupl=='dupl' and isinstance(node, Node):
      return Formula(node)

  def replace_nodes_at(self, pos_li: List[List[int]],
                      new_node_li, dupl: str=''):
    node = self.ast.replace_nodes_at(pos_li, new_node_li, dupl)
    if dupl=='dupl' and isinstance(node, Node):
      return Formula(node)

  def substitute(self, var: str, new_node, dupl: str = ''):
    # Use Node.substitute() method.
    # var can be either is individual var/constant or propositional var.
    node = self.ast.substitute(var, new_node, dupl) 
    if dupl=='dupl' and isinstance(node, Node):
      return Formula(node)

  # Methods for building truth tables.

  #region comment1
  # We want to be able to construct truth tables for 
  #  (1) not only propositional formulas built from prop letters 
  #      and connectives, but also first order formulas,
  #  (2) not only just for single formulas but also sets of formulas.
  
  # For example, in order to determine whether {alpha, beta} proves phi
  # is justified by tautological consequence, we would need to be able 
  # to construct a truth table for {alpha, beta, not phi}.  That's why
  # we need (2).
  
  # For (1), we need to be able to identify prime subformulas, which are
  # the atoms of propositional reasoning.  These can be identified in the
  # AST of a formula with bottom-up method. See the following code for details.

  # Note that the prime formulas are represented in the code by the 
  # infix-notation strings of the formulas.  This is because we want to be 
  # able to use set operations, and the Nodes of the AST are not hashable.

  # Prime subformulas are the subformulas having the root whose token_type
  # belongs to PRIME_ROOT := ("pred_pre", "pred_in", "equality", 
  #    "prop_letter", "quantifier", "conn_0ary"), or equivalently,
  # whose token_type does not belong to 
  #   NON_PRIME_ROOTS := ("conn_1ary", "conn_2ary", "conn_arrow")
  #endregion comment1

  def get_prime_subformulas(self) -> set:
    MAX_N = 8 # maximum number of prime subformulas
    prime_subs = set()
    tree = self.ast
    if tree.token.token_type in Token.NON_PRIME_ROOTS: 
      # connectives of positive arity
      for kid in tree.children:
        prime_subs |= Formula(kid).get_prime_subformulas()
    elif tree.token.token_type != 'conn_0ary':
      prime_subs |= { self.ast.build_infix('text') }

    assert len(prime_subs) <= MAX_N, \
      f"Error: number of prime subformulas exceeds {MAX_N}."
    return prime_subs
  
  #region comment2
  # Truth tree is a subtree of the AST of a formula.
  # Each node in the truth tree is a subformula of the formula,
  # where the subformula is a prime subformula or a subformula built
  # from earlier nodes in the truth tree and connectives.
  # In short, a truth tree is a tree of subformulas where each node
  # is to be assigned a truth value.

  # bot, the constant False, is a prime subformula, but it is not
  # in prime_subs for a technical reason.

  # For example, if forall x P(x) imp Q is a formula,
  # among the 4 subformulas, forall x P(x) and Q are prime subformulas,
  # 3 are nodes in the truth tree, and 1, P(x) is not.

  # Prime nodes of the truth tree should be given indices.
  # We define the prime nodes to be the nodes corresponding to the 
  # elements of prime_subs, which is the set of all prime subformulas
  # except bot.

  # For example, if [A, forall x P(x), Q(x,y)] is a prime_subs_li of a
  # given set of formulas, then any node of the truth tree of a formula, 
  # whose label is A is assigned index 0. Similarly,
  # forall x P(x) is assigned index 1, and Q(x,y) is assigned index 2.
  # Only the prime nodes in the truth tree are assigned indices.
  #endregion comment2

  def label_prime_subs(self, prime_subs_li: List[str]) -> None:
    # In this method, each prime node in a truth tree is assigned 
    # an index, which is the index of the formula in prime_subs_li.
    # Also, each prime node which is not a prop letter is assigned 
    # an alternate label P_1, P_2, etc. to its property 
    # node.alt_str. So, prop letter P_i is not allowed for any formula.
    
    dict_index2i = dict()
    n_added_alt = 0

    def rec_fn(node: Node) -> None:
      nonlocal n_added_alt
      if node.token.token_type in Token.NON_PRIME_ROOTS:
        for kid in node.children:
          rec_fn(kid)
      elif node.token.token_type != 'conn_0ary':
        node.index = prime_subs_li.index(node.build_infix('text'))         
        if node.token.token_type != 'prop_letter':
          if node.index not in dict_index2i:
            n_added_alt += 1
            dict_index2i[node.index] = (i := n_added_alt)
            node.alt_str = f"P_{i}"
          else:
            i = dict_index2i[node.index] 
            node.alt_str = f"P_{i}"
        else:
          node.alt_str = node.token.value

    rec_fn(self.ast)

  def get_truth_tree(self, tVal_assign: str) -> None:
    # tVal_assign is a truth-value assignment, represented by 
    # a string of 0's and 1's, for prime subformulas.
    # For bot, the constant False, we always assign 0.
    # The length of tVal_assign is the same as the length of 
    # prime_subs_li, denoted by n.
    # For inner nodes of the truth tree, their bValues are assigned
    # by the truth values of their children and their connectives.
    # This method is called after label_prime_subs() is called.
    # To build a truth table, this method need be called 2^n times.
    # Note that label_prime_subs() is called only once.
    # After this method is called, the truth trees consists of nodes
    # with bValues assigned.

    node = self.ast
    if node.token.token_type in Token.NON_PRIME_ROOTS: # non-prime subformula
      # do the job for the children of the node first
      for node_i in node.children:
        Formula(node_i).get_truth_tree(tVal_assign)
      # then do the job for the node itself
      token_value = node.token.value
      if token_value == 'not':
        node.bValue = 1 - node.children[0].bValue
      elif token_value == 'and':
        node.bValue = min(int(node.children[0].bValue), node.children[1].bValue)
      elif token_value == 'or':
        node.bValue = max(int(node.children[0].bValue), node.children[1].bValue)
      elif token_value == 'imp':
        node.bValue = max(1 - node.children[0].bValue, 
                          int(node.children[1].bValue))
      elif token_value == 'iff':
        node.bValue = 1 - abs(node.children[0].bValue - 
                              node.children[1].bValue)
      elif token_value == 'xor':
        node.bValue = abs(node.children[0].bValue - 
                          node.children[1].bValue)
      else:
        print(f"Error: unknown connective \"{token_value}\".")
    else: # prime subformula
      if node.index >= 0: # in prime_subs_li
        node.bValue = int(tVal_assign[node.index])
      else: # node.index == -1 which means node is bot
        node.bValue = 0

  def get_bValues(self) -> List[int]:
    # This method is called right after get_truth_tree() is called
    # so that all (subformula) nodes in the truth tree have been 
    # assigned bValues before this method is called.
    # This method returns a list of truth values of the nodes
    # in the infix notation order. In-order traversal of the truth tree
    # is used.
    
    bValues = []
    tree = self.ast
    token = tree.token
    if token.token_type in Token.FMLA_ROOTS:
      if token.token_type in Token.NON_PRIME_ROOTS:
        if token.arity == 1:
          bValues.append(tree.bValue)
          bValues += Formula(tree.children[0]).get_bValues()
        else: # token.arity == 2
          bValues += Formula(tree.children[0]).get_bValues()
          bValues.append(tree.bValue)
          bValues += Formula(tree.children[1]).get_bValues()
      else: # token.token_type in Token.PRIME_ROOTS
        bValues.append(tree.bValue)

    return bValues
  # end of class Formula

FList = List[Formula]

class Truth_table:
  def  __init__(self, f_list: FList):
    self.f_list = f_list

  def get_prime_subformulas(self) -> set:
    MAX_N = 8 # maximum number of prime subformulas
    prime_subs = set()
    for f in self.f_list:
      prime_subs |= f.get_prime_subformulas()

    assert len(prime_subs) <= MAX_N, \
      f"Error: number of prime subformulas exceeds {MAX_N}."
    return prime_subs

  def label_prime_subs(self, prime_subs_li: List[str]) -> None:
    # In this method, each prime node in a truth tree is assigned 
    # an index, which is the index of the formula in prime_subs_li.
    # Also, each prime node which is not a prop letter is assigned 
    # an alternate label P_1, P_2, etc. to its property 
    # node.alt_str. So, prop letter P_i is not allowed for any formula.
    
    dict_index2i = dict()
    n_added_alt = 0

    def rec_fn(node: Node) -> None:
      nonlocal n_added_alt
      if node.token.token_type in Token.NON_PRIME_ROOTS:
        for kid in node.children:
          rec_fn(kid)
      elif node.token.token_type != 'conn_0ary':
        node.index = prime_subs_li.index(node.build_infix('text'))         
        if node.token.token_type != 'prop_letter':
          if node.index not in dict_index2i:
            n_added_alt += 1
            dict_index2i[node.index] = (i := n_added_alt)
            node.alt_str = f"P_{i}"
          else:
            i = dict_index2i[node.index] 
            node.alt_str = f"P_{i}"
        else:
          node.alt_str = node.token.value

    for f in self.f_list:
      rec_fn(f.ast)

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
