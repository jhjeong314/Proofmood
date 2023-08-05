from typing import List, Tuple

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

    if opt in {'latex', 'text'}:
      self.ast.display_infix(opt)
    else: # truth_table case {'truth_table', 'truth_table_str'}
      # 1. label_prime_subs(prime_subs_li) should be called in advance.
      # 2. This case returns a string instead of printing it out.
      new_ast = copy.deepcopy(self.ast)
      def rec_fn(node: Node) -> None:
        if node.token.token_type in Token.NON_PRIME_ROOTS:
          for kid in node.children:
            rec_fn(kid)
        elif node.token.token_type != 'conn_0ary': 
          # node must be prime subformula
          # convert "P_n" to "Pn"
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
      if opt == 'truth_table':
        new_fmla.display_infix('text')
      elif opt == 'truth_table_str':
        return new_fmla.ast.build_infix('text')

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
    # This method is used in FormulaList.get_prime_subformulas().
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

  def label_prime_subs(self, prime_subs_li: List[str]) -> List[str]:
    # This method uses FormulaList.label_prime_subs().
    t_table = FormulaList([self])
    return t_table.label_prime_subs(prime_subs_li)

  def show_p_sub_labels(self, prime_subs_li: List[str]) -> None:
    # This method uses FormulaList.show_p_sub_labels().
    t_table = FormulaList([self])
    t_table.show_p_sub_labels(prime_subs_li)

  def assign_levels(self) -> None:
    # This method is used in FormulaList.assign_levels().
    # It assigns levels to the prop. nodes of the truth tree.
    # Prop. letters and bots are assigned level 1.
    # not A gets level n+1 where n = level of A.
    # If * is one of and, or, imp, iff, xor, then A * B gets level 
    # max(n,m)+1, where n = level of A, m = level of B.

    MAX_LEVEL = 9
    node = self.ast
    if node.token.token_type in Token.NON_PRIME_ROOTS: 
      # non-prime subformula
      # do the job for the children of the node first
      for node_i in node.children:
        Formula(node_i).assign_levels()
      # then do the job for the node itself
      kid1 = node.children[0]
      level1 = int(kid1.level)
      if node.token.arity == 1:
        node.level = level1 + 1
      else: # arith == 2
        kid2 = node.children[1]
        level2 = int(kid2.level)
        node.level = max(level1, level2) + 1
      if node.level >= MAX_LEVEL:
        print(f"Error: level of a node exceeds {MAX_LEVEL}.")
    else: # prime subformula
      node.level = 1

  def get_truth_tree(self, tVal_assign: str) -> None:
    # This method is used in FormulaList.get_truth_tree().
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
      kid1 = node.children[0]
      level1 = int(kid1.level)
      if token_value == 'not':
        node.bValue = 1 - kid1.bValue
        node.level = kid1.level + 1
      else:
        kid2 = node.children[1]
        level2 = int(kid2.level)
        node.level = max(level1, level2) + 1
        if token_value == 'and':
          node.bValue = min(int(kid1.bValue), kid2.bValue)
        elif token_value == 'or':
          node.bValue = max(int(kid1.bValue), kid2.bValue)
        elif token_value == 'imp':
          node.bValue = max(1 - kid1.bValue, int(kid2.bValue))
        elif token_value == 'iff':
          node.bValue = 1 - abs(kid1.bValue - kid2.bValue)
        elif token_value == 'xor':
          node.bValue = abs(kid1.bValue - kid2.bValue)
        else:
          print(f"Error: unknown connective \"{token_value}\".")
    else: # prime subformula
      node.level = 0
      if node.index >= 0: # in prime_subs_li
        node.bValue = int(tVal_assign[node.index])
      else: # node.index == -1 which means node is bot
        node.bValue = 0

  def get_bValues(self, opt: str='truth_val') -> List[int]:
    # opt ::== 'truth_val' | 'level'
    # For opt == 'truth_val', this method is used in
    # Truth_value.show_truth_table().
    # This method is called right after get_truth_tree() is called
    # so that all (subformula) nodes in the truth tree have been 
    # assigned bValues before this method is called.
    # This method returns a linear list (in the infix notation order)
    # of truth values of the tree nodes. 
    # In-order traversal of the truth tree is used.
    # For opt == 'level', we use tree.level instead of tree.bValue.
    # level could be 0, 1, 2, ... while bValue is 0 or 1.
    # That's all the difference between the two cases.
    
    bValues = []
    tree = self.ast
    token = tree.token
    if token.token_type in Token.FMLA_ROOTS:
      if token.token_type in Token.NON_PRIME_ROOTS:
        if token.arity == 1:
          v = tree.bValue if opt=='truth_val' else tree.level
          bValues.append(v)
          bValues += Formula(tree.children[0]).get_bValues(opt)
        else: # token.arity == 2
          bValues += Formula(tree.children[0]).get_bValues(opt)
          v = tree.bValue if opt=='truth_val' else tree.level
          bValues.append(v)
          bValues += Formula(tree.children[1]).get_bValues(opt)
      else: # token.token_type in Token.PRIME_ROOTS
          v = tree.bValue if opt=='truth_val' else tree.level
          bValues.append(v)

    return bValues
  
  def show_truth_table(self, opt: str='text') -> None:
    # opt ::== 'text' | 'latex'
    # This method uses FormulaList.show_truth_table().
    t_table = FormulaList([self])
    t_table.show_truth_table(opt)

  # end of class Formula

FList = List[Formula]

class FormulaList:
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

  def label_prime_subs(self, prime_subs_li: List[str]) -> List[str]:
    # In this method, each prime node in a truth tree is assigned 
    # an index, which is the index of the formula in prime_subs_li.
    # Also, each prime node which is not a prop letter is assigned 
    # an alternate label P_1, P_2, etc. to its property 
    # node.alt_str. For prop letter node, node.alt_str is set to
    # the prop letter itself, i.e., node.token.value.
    # So, when forming any formula, prop letter P_i is not allowed.
    # The return value is the list of alternate labels of the prime nodes.
    
    dict_index2i = dict()
    ret_li = [''] * len(prime_subs_li)
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
            ret_li[node.index] = node.alt_str
          else:
            i = dict_index2i[node.index] 
            node.alt_str = f"P_{i}"
        else:
          node.alt_str = node.token.value 
          # What if node.token.value has '_' and/or too long?
          ret_li[node.index] = node.alt_str

    for f in self.f_list:
      rec_fn(f.ast)
    return ret_li

  def show_p_sub_labels(self, prime_subs_li: List[str]) -> None:
    # This method prints out the prime subformulas and their labels
    # for each formula in self.f_list.
    def rec_fn(node: Node) -> None:
      if node.token.token_type in Token.NON_PRIME_ROOTS:
        for kid in node.children:
          rec_fn(kid)
      else:
        if node.alt_str.startswith('P_'):
          if node.alt_str not in labels_done:
            print(f"{node.alt_str}: {node.build_infix('text')}")
            labels_done.append(node.alt_str)

    labels_done = []

    for f in self.f_list:              
      rec_fn(f.ast)

  def assign_levels(self) -> None:
    # This is a very simple method.  It just calls 
    # Formula.assign_levels() for each formula in self.f_list.
    for f in self.f_list:
      f.assign_levels()    

  def get_truth_tree(self, tVal_assign: str) -> None:
    # This is a very simple method.  It just calls 
    # Formula.get_truth_tree() for each formula in self.f_list.
    for f in self.f_list:
      f.get_truth_tree(tVal_assign)
  
  def get_binary(self, n: int, len: int) -> str:
    # This method is used in show_truth_table().
    # n is an integer in the range [0, 2^len - 1]
    # len is the number of propositional letters in the formula(s)
    # E.g., if n=5, len=4, then return '0101'.
    return bin(n)[2:].zfill(len)
  
  def print_truth_table_row(self, header: str, tVal_assign: str, 
                             bValues: List[int]) -> None:
    # This method is used in show_truth_table(opt='text') to print
    # a row of the table corresponding to tVal_assign. So, this method
    # will be called 2^n_prop_letters times to complete the table.
    # The truth values, 0 and 1, in the row are printed in line with 
    # the tokens in the header.

    # The header argument is only used to determine the positions of the
    # 0's and 1's in the row. So it is inefficient to pass the header
    # argument to this method and compute the positions every time,
    # because this method is called 2^n_prop_letters times.
    # But, for the sake of simplicity, we do it this way for now.

    SEP_CHAR = ' (),:'

    # This method is used for printing the footer as well.
    # tVal_assign consists of 0's and 1's for the row case
    # and 2's for the footer case.
    bFooter = '2' in tVal_assign # tVal_assign == '22..2'

    tvSeq = list(tVal_assign) + [str(i) for i in bValues]
      # tvSeq = truth value sequence
    str_li = [] # list of strings '0', '1', ' '+ 
                # to be joined and then printed
    pos = 0 # position in header
    len_sp = 0 # length of space between adjacent truth values
    i = 0 # index in tvSeq
    while pos < len(header):
      c = header[pos]
      pos += 1
      if c in SEP_CHAR:
        len_sp += 1
      else:
        pos_s = pos
        while pos < len(header) and header[pos] not in SEP_CHAR:
          pos += 1
        pos_e = pos
        word_len = pos_e - pos_s + 1
        padding_left = ' ' * (len_sp + (word_len-1) // 2)
        padding_right = ' ' * (word_len // 2)
        str_li.append(padding_left + tvSeq[i] + padding_right)
        i += 1
        len_sp = 0

    footer_str = ''.join(str_li)
    if bFooter:
      prefix_len = footer_str.index('1')
      bVal_str = footer_str[prefix_len:]
      prefix = "Level".ljust(prefix_len)
      footer_str = prefix + bVal_str
    print(footer_str)

  def print_latex_row(self, empty_pos_li: List[int], tvSeq: List[str], 
                      bLast: bool=False) -> None:
    for pos in empty_pos_li:
      tvSeq.insert(pos, '')

    for i, s in enumerate(tvSeq):
      if i > 0:
        tvSeq[i] = ' & ' + s

    postfix = r" \\ \hline" if bLast else r" \\"
    print(''.join(tvSeq) + postfix)
    
  def print_truth_table_footer(self, header: str, n: int,
                             bValues: List[int]) -> None:
    v_str = '2' * n # n = number of propositional letters
    self.print_truth_table_row(header, v_str, bValues)

  def get_header_latex(self, header: str) -> Tuple[str, List[int]]:
    v_li = header.split()
    elt_lit = [r"\begin{tabular}{|"]
    for s in v_li:
      if s == ':':
        elt_lit.append(r"|")
      elif s.endswith(','):
        elt_lit.append(r"c||")
      elif s.startswith('(') or s.endswith(')'):
        elt_lit.append(r"c|c|")
      else:
        elt_lit.append(r"c|")
    elt_lit.append(r"}\hline" + "\n")

    begin_tabular = "".join(elt_lit)

    v_li2 = []      
    for s in v_li:
      if s == ':':
        pass
      elif s.endswith(','):
        v_li2.append(s[:len(s)-1])
      elif s.startswith('('):
        v_li2.append('(')
        v_li2.append(s[1:])
      elif s.endswith(')'):
        v_li2.append(s[:len(s)-1])
        v_li2.append(')')
      else:
        v_li2.append(s)

    L_DICT = dict(
          [("not", r"\neg"), ("and", r"\wedge"), ("or", r"\vee"),
          ("imp", r"\to"), ("iff", r"\leftrightarrow"),
          ("xor", r"\nleftrightarrow")])

    v_li3 = []
    for s in v_li2:
      if s in L_DICT:
        s2 = L_DICT[s]
      elif s[0]=='P' and s[1] in "12345678" and len(s)==2:
        s2 = s[0] + "_" + s[1]
      else:
        s2 = s
      v_li3.append('$' + s2 + '$')

    for i, s in enumerate(v_li3):
      if i > 0:
        v_li3[i] = ' & ' + s
      if i % 8 == 7:
        v_li3[i] = ' & ' + s + "\n"

    header_row = ''.join(v_li3) + r" \\ \hline"
    header_latex = begin_tabular + header_row

    empty_pos_li = []
    for i, s in enumerate(v_li2):
      if s in "()":
        empty_pos_li.append(i)

    return (header_latex, empty_pos_li)

  def show_truth_table(self, opt: str='text') -> None:
    # opt ::== 'text' | 'latex'
    # For opt == 'text', this method generates and prints out a truth 
    # table for the formulas in self.f_list.
    # For opt == 'latex', this method prints out the LaTeX source code.
    # It doesn't render the table on the screen.

    # Roughly speaking, it uses the following methods to prepare the 
    # scaffold of the truth tree.
    # 1. get_prime_subformulas()
    # 2. label_prime_subs(prime_subs_li)
    # Then, for each truth value assignment, it uses the following
    # methods to fill in the truth tree.
    # 3. get_truth_tree(tVal_assign)
    # Finally, for each truth value assignment, it uses the following
    # methods to print out a row of the truth table.
    # 4. get_bValues()
    # 5. print_truth_table_row()
    
    prime_subs_li = list(self.get_prime_subformulas())
    alt_str_li = self.label_prime_subs(prime_subs_li)
    id = list(range(len(prime_subs_li))) # identity permutation
    # say len(prime_sub_li) == 4, then id == [0, 1, 2, 3]
    perm = [j for _, j in sorted(zip(alt_str_li, id))] # permutation
    alt_str_li2 = sorted(alt_str_li)
         
    n_fmla = len(self.f_list)
    print("Truth table for the following", end="")
    print(" formula." if n_fmla == 1 else f" {n_fmla} formulas.")

    for f in self.f_list:
      f.display_infix()
    # self.show_p_sub_labels(prime_subs_li)
    # print("")

    # Show prime subformulas and their alternate labels.
    n_prime_node = len(prime_subs_li)
    prime_subs_li2 = [prime_subs_li[perm[j]] for j in range(n_prime_node)]
    if opt == 'text':
      print("prime subformulas =", prime_subs_li2)
      print("alt prop. letters =", alt_str_li2)
      print()
    else: # opt == 'latex'
      print("Prime subformulas and their alternate labels.")
      Node.display_latex_li(prime_subs_li2)
      Node.display_latex_li(alt_str_li2)

    # Prepare and print the header of the truth table.
    str_li = [str(f.display_infix('truth_table_str')) 
              for f in self.f_list]
    formulas_joined = ', '.join(str_li)
    prop_letters = ' '.join(alt_str_li2)
    header = f"{prop_letters.replace('_','')} : {formulas_joined}"
    if opt == 'text':
      # Print the header.
      print(f"{header}")
      print(f"{'-' * len(header)}")
    else: # opt == 'latex'
      header_latex, empty_pos_li = self.get_header_latex(header)
      print(header_latex)
      # print(empty_pos_li)

    # Generate and print out the body of the truth table.
    n_row = 2**n_prime_node
    for i in range(1, n_row+1):
      tVal_assign = self.get_binary(n_row - i, n_prime_node)
      # Start from 11..1 and go down to 00..0.
      tVal = ''.join([tVal_assign[perm[j]] for j in range(n_prime_node)])
      self.get_truth_tree(tVal)
      bValues = []
      for f in self.f_list:
        bValues += f.get_bValues()
      if opt == 'text':
        self.print_truth_table_row(header, tVal_assign, bValues)
      else: # opt == 'latex':
        tvSeq = list(tVal_assign) + [str(i) for i in bValues]
        self.print_latex_row(empty_pos_li, tvSeq, i == n_row) # pyright: ignore[reportUnboundVariable]  

    # Print the footer of the truth table.
    self.assign_levels()
    bValues = []
    for f in self.f_list:
      bValues += f.get_bValues('level')
    if opt == 'text':
      print(f"{'-' * len(header)}")
      self.print_truth_table_footer(header, n_prime_node, bValues)
    else: # opt == 'latex':
      # self.print_truth_table_footer(header, n_prime_node, bValues)
      print(r"\end{tabular}")
      
  # end of class FormulaList

# Utility function

def show_tree_nodes(tree: Node) -> None: # 
# This function closely follows the code of Formula.get_bValues(), 
# utilizing an in-order traversal approach.
# This function should be called after label_prime_subs() 
# has been called.
# Each prime node is labeled with alt_str, which is a short string
# to represent the prime subformulas.  For instance suppose that
# a formula phi has forall x (A(x) imp B(x)) as a prime subformula.
# Then, in building the truth table for phi, we can represent phi
# as a single propositional letter, say P1.  This "P1" is the alt_str
# of the prime node for forall x (A(x) imp B(x)).
# This function shows id, bValue (which is not assigned yet), and
# alt_str of each node.

  def show_this_node(node: Node):
    print(f"{node.token.value}, id={node.index}, " +
      f"bVal={node.bValue}, level={node.level}, alt_str={node.alt_str}")

  token = tree.token
  if token.token_type in Token.FMLA_ROOTS:
    if token.token_type in Token.NON_PRIME_ROOTS:
      if token.arity == 1:
        show_this_node(tree) # unary connective is prefixed
        show_tree_nodes(tree.children[0])
      else: # arity == 2
        show_tree_nodes(tree.children[0])
        show_this_node(tree) # binary connective is infixed
        show_tree_nodes(tree.children[1])
    else: # token_type in PRIME_ROOT
      show_this_node(tree)
