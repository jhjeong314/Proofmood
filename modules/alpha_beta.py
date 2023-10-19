from typing import List, Tuple
import math, random, copy, graphviz 
from pprint import pprint

class Node:
  #region trivial methods
  def __init__(self, value: float | None = None, children=None):
    self.value = value
    self.evaluated = False
    self.children = children or [] # list of Node objects
  
  def is_terminal(self):
    return not self.children
  
  def get_children(self):
    return self.children
  
  def evaluate(self):
    self.evaluated = True
    return self.value
  
  def num_nodes(self):
    if self.is_terminal():
      return 1
    else:
      return 1 + sum([kid.num_nodes() for kid in self.children])
  
  def __str__(self):
    return self.build_str(opt='all')
  #endregion trivial methods

  def build_str(self, prefix: str='[] ', opt=''):
    # depth of self >= 1 is assumed.
    # opt=='all': print all nodes
    # else: do not print unevaluated nodes
    if self.is_terminal():
      return prefix + str(self.value) + "\n"
    else:
      if opt!='all' and not self.evaluated:
        return prefix + 'unevaluated' + "\n"
      else:
        str1_li = [prefix + str(self.value) + "\n"]
        for i, kid in enumerate(self.children):
          prefix_new = prefix[:-2] + str(i) + '] '
          #^ '[ab] ' => '[abi] '
          if opt!='all' and not kid.evaluated:
            str1_li.append(prefix_new + 'unevaluated' + "\n")
          else:
            str1_li.append(kid.build_str(prefix_new, opt))
        return ''.join(str1_li)
    
  def draw_tree(self, bMaximizer=True, verbose=False) -> None:
    # self must be the root node
    # You can call this method before or after evaluation, 
    # that is, before or after minimax/alpha-beta.
    # bMaximizer: True/False if the maximizer/minimizer plays first.
    # before evaluation (root.evaluated == False):
    #   None nodes are labeled with Max/Min.
    #   So, only the terminal nodes are labeled with values.
    # after evaluation (root.evaluated == True):
    #   unevaluated nodes are labeled with Max/Min.
    #   This reveals the pruning for alpha-beta.
    #   For minimax, bMaximizer doesn't matter because no node
    #   is labeled with Max/Min anyway.

    from IPython.display import display

    prefix = "graph {\n"
    suffix = "}"
    # Set display options depending on the size of the tree.
    if self.num_nodes() < 16:
      option_str = \
        "  node [width=.4 height=.4 fixedsize=true fontsize=12];\n" + \
        "  nodesep=0.2;\n  ranksep=0.2;\n\n"
      max_str = "Max"
      min_str = "Min"
    else:
      option_str = \
        "  node [width=.25 height=.3 fixedsize=true fontsize=10];\n" + \
        "  nodesep = 0.2;\n  ranksep = 0.2;\n\n"
      max_str = "max" # "↑"
      min_str = "min" # "↓"

    def build_labels_rec(node, bMaximizer, prefix: str = '') -> str:
      # bMaximizer: True/False if the maximizer/minimizer plays first.      
      node_index = prefix if prefix != '' else 'root'
      ret_str_li = ['  ', node_index, ' [label="']

      # output a line for this node
      color_str = ''
      if (not self.evaluated and node.value is None or
          self.evaluated and not node.evaluated):
        label = max_str if bMaximizer else min_str
        if self.evaluated:
          color_str = ' fontcolor="red"'
      else:
        label = str(node.value)
      ret_str_li.append(label + '"' + color_str + '];\n')

      # output lines for children nodes
      for i, kid in enumerate(node.children):
        ret_str_li += build_labels_rec(kid, not bMaximizer, 
                                       prefix + str(i))
      return ''.join(ret_str_li)

    def build_relations_rec(node: Node, prefix: str = '') -> str:
      assert not node.is_terminal(), \
        "build_relation_rec(): node cannot be terminal"

      node_index = prefix if prefix != '' else 'root'
      ret_str_li = ['  ', node_index, ' -- {']

      # output a line for this node
      for i, kid in enumerate(node.children):
        separator = ' ' if i > 0 else ''
        ret_str_li.append(separator + prefix + str(i))
      ret_str_li.append('};\n')

      # output lines for children nodes
      for i, kid in enumerate(node.children):
        if not kid.is_terminal():
          ret_str_li.append(build_relations_rec(kid, prefix + str(i)))

      return ''.join(ret_str_li)
  
    labels_str = build_labels_rec(self, bMaximizer, '') + "\n"
    relations_str = build_relations_rec(self)
    dot_data = prefix + option_str + labels_str + relations_str + suffix

    if verbose:
      print(dot_data)
    graph = graphviz.Source(dot_data)
    display(graph)

def build_bin_tree(input: int | List[int] = 3) -> Node:  
  # When input is an integer k, we build a full binary tree such that
  # all terminal nodes have depth k.  All non-terminal nodes are labeled 
  # with None. All terminal nodes are labeled with some random integers.

  # When input is li: List[int], we work with a deep-copied clone of 
  # input so that input is not mutated. 
  # In this case, len(li) must be 2 ** k for some k, and
  # we build a binary tree where all terminal nodes have depth k.
  # All non-terminal nodes are labeled with None. All terminal nodes
  # are labeled with elements of li.

  if isinstance(input, int):
    tree_depth = input
    assert 1 <= tree_depth <= 4, ' 1 <= tree_depth <= 4 must hold.'
    max_val = int(round(2 ** tree_depth * 0.76))
    terminal_label_li = [random.randint(1, max_val) 
                         for _ in range(2 ** tree_depth)]
  elif (isinstance(input, list) and len(input) > 0 and
        all([isinstance(x, int) for x in input])):
    terminal_label_li = copy.deepcopy(input)
    alert_msg = 'terminal_label_li must have length 2 ** tree_depth.'
    len_li = len(terminal_label_li)
    tree_depth = math.log2(len_li)
    assert math.ceil(tree_depth) == math.floor(tree_depth), alert_msg
  else:
    raise ValueError('input must be an integer or a list of integers.')

  def build_bin_tree_rec(depth: int) -> Node:
    if depth == tree_depth:
      if terminal_label_li:
        return Node(terminal_label_li.pop(0)) # pop from the left
      else:
        return Node()
    else:
      return Node(children=[build_bin_tree_rec(depth+1),
                            build_bin_tree_rec(depth+1)])
    
  return build_bin_tree_rec(0)    

def build_my_tree(terminal_label_li: List[int] = []) -> Node:
  if not terminal_label_li:
    terminal_label_li = [random.randint(1, 11) for _ in range(16)]
  assert len(terminal_label_li) == 16, \
    'build_my_tree(): there must be 16 terminal nodes'
  # Build a tree of a fixed structure.
  node0000 = Node(terminal_label_li[0])
  node0001 = Node(terminal_label_li[1])
  node000 = Node(children=[node0000, node0001])
  node0010 = Node(terminal_label_li[2])
  node0011 = Node(terminal_label_li[3])
  node0012 = Node(terminal_label_li[4])
  node0013 = Node(terminal_label_li[5])
  node001 = Node(children=[node0010, node0011, node0012, node0013])
  node00 = Node(children=[node000, node001])
  node0100 = Node(terminal_label_li[6])
  node010 = Node(children=[node0100])
  node01 = Node(children=[node010])
  node0 = Node(children=[node00, node01])
  node1000 = Node(terminal_label_li[7])
  node100 = Node(children=[node1000])
  node1010 = Node(terminal_label_li[8])
  node1011 = Node(terminal_label_li[9])
  node101 = Node(children=[node1010, node1011])
  node10 = Node(children=[node100, node101])
  node1100 = Node(terminal_label_li[10])
  node1101 = Node(terminal_label_li[11])
  node110 = Node(children=[node1100, node1101])
  node1110 = Node(terminal_label_li[12])
  node111 = Node(children=[node1110])
  node11 = Node(children=[node110, node111])
  node1 = Node(children=[node10, node11])
  node2000 = Node(terminal_label_li[13])
  node200 = Node(children=[node2000])
  node20 = Node(children=[node200])
  node2100 = Node(terminal_label_li[14])
  node2101 = Node(terminal_label_li[15])
  node210 = Node(children=[node2100, node2101])
  node21 = Node(children=[node210])
  node2 = Node(children=[node20, node21])
  node = Node(children=[node0, node1, node2])
  return node

  raise NotImplementedError('build_my_tree() is not implemented.')

def minimax(node: Node, toMaximize: bool, move_path: List[int] = []) \
            -> Tuple[float | None, List[int]]:
  # Recursive implementation of minimax algorithm.
  # node: the root node of the tree to be evaluated.
  # toMaximize: True if the maximizer plays first.
  # move_path: list of indices of children nodes to be taken
  #            to reach the current node from the root node.
  # Return value is the tuple 
  #   (value of the node after minimax, the move_path to the node).

  # The 'depth' parameter that is usually used in minimax() algorithm
  # is omitted here.  This is because the evaluation of a node is 
  # simply node.value, which is given to terminal nodes only.
  
  # Non-terminal nodes are assumed to be labeled with None, and
  # will be labeled with the value of the node after minimax.

  # Node is mutated by this function: for all descendant nodes of the 
  # input node, node.evaluated is set to True, and node.value is set 
  # to the value of the node after minimax. A node is a descendant of 
  # itself of course.


  if node.is_terminal():
    val = node.evaluate()
    if val is None:
      raise ValueError('None encountered at terminal node.')
    return val, []

  node.evaluated = True
  if toMaximize:
    max_val = float('-inf')
    move_path0 = []
    for i, child in enumerate(node.get_children()):
      val, move_path = minimax(child, False, move_path)
      assert val is not None
      if val > max_val:
        max_val = val
        move_path0 = [i] + move_path
    node.value = max_val 
    #^ not necessary for minimax. for visualization only
    return max_val, move_path0
  else:
    min_val = float('inf')
    move_path0 = []
    for i, child in enumerate(node.get_children()):
      val, move_path = minimax(child, True, move_path)
      assert val is not None
      if val < min_val:
        min_val = val
        move_path0 = [i] + move_path
    node.value = min_val 
    #^ not necessary for minimax. for visualization only
    return min_val, move_path0

# Fail-soft version of alpha-beta pruning is given below.
# For fail-hard version, see https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning#Pseudocode

def alpha_beta_pruning(node: Node, toMaximize: bool,
    alpha: float = float('-inf'), beta: float = float('inf'),
    move_path: List[int] = []) -> Tuple[float | None, List[int]]:
  # alpha: the minimum value that the maximizer is assured
  # beta: the maximum value that the minimizer is assured
  # alpha, beta are not properties of nodes, but sort of a global 
  # variable that is passed along the computation process.
  
  # Node is mutated by this function: for all descendant nodes of the 
  # input node, except those descendants that belong to pruned branches,
  # node.evaluated is set to True, and node.value is set to the value 
  # of the node after minimax.
  
  if node.is_terminal():
    val = node.evaluate()
    if val is None:
      raise ValueError('None encountered at terminal node.')
    return val, []

  node.evaluated = True
  i = 0
  if toMaximize:
    # print(f"(maximize) alpha: {alpha}, beta: {beta}")
    max_val = float('-inf') # for the children of this node
    move_path0 = []
    for i, child in enumerate(node.get_children()):
      val, move_path = alpha_beta_pruning(child, False, alpha, beta, move_path)
      assert val is not None
      if val > max_val:
        max_val = val
        move_path0 = [i] + move_path
        # alpha, passed from the parent, is updated here
        alpha = max(alpha, val) 
        # beta is passed from the minimizing parent
        if val >= beta: 
          # The parent will not use max_val because it is a minimizer.
          # Further search is futile because it can only make max_val, 
          # the return value larger.
          break
    node.value = max_val # for visualization only
    return max_val, move_path0
  else:
    # print(f"(minimize) alpha: {alpha}, beta: {beta}")
    min_val = float('inf') # for the children of this node
    move_path0 = []
    for i, child in enumerate(node.get_children()):
      val, move_path = alpha_beta_pruning(child, True, alpha, beta, move_path)
      assert val is not None
      if val < min_val:
        min_val = val
        move_path0 = [i] + move_path
        # beta, passed from the parent, is updated here
        beta = min(beta, val)
        # alpha is passed from the maximizing parent
        if val <= alpha: 
          # The parent will not use min_val because it is a maximizer.
          # Further search is futile because it will only make min_val,
          # the return value smaller.
          break
    node.value = min_val # for visualization only
    return min_val, move_path0
                  