#region 0 
from typing import List, Tuple, Dict, Set, Any
import re
import sys
sys.path.append('/Users/jooheejeong/Documents/Work/Proofmood/logical_formulas')
from first_order_logic_parse import *
from truth_table import * 
from enum import Enum

class Connective(Enum):
  BOT = 'bot'
  NOT = 'not'
  AND = 'and'
  OR = 'or'  
  IMP = 'imp'
  IFF = 'iff'

class RuleInfer(Enum):
  BOT_INTRO = 1
  BOT_ELIM = 2
  NOT_INTRO = 3
  NOT_ELIM = 4
  AND_INTRO = 5
  AND_ELIM = 6
  OR_INTRO = 7
  OR_ELIM = 8
  IMP_INTRO = 9
  IMP_ELIM = 10
  IFF_INTRO = 11
  IFF_ELIM = 12
  REPEAT = 13
  LEM = 14
  HYP = 15

CONN_LIST = [conn.value for conn in Connective]
INTRO_ELIM = ['intro', 'elim']
RULES_AUX = ['repeat', 'LEM', 'hyp']
VERT = '│'
PROVES = '├─'
TAB = '\t'
#endregion 0

class FormulaProp(Formula):
  def __init__(self, input: str | Node):
        super().__init__(input)

  def is_fmla_type(self, fmla_type: Connective) -> bool:
    return self.ast.token.value == fmla_type.value
  
  def get_kid_node1(self) -> Node:
    """ Get the kid node of self, which is a negation formula. """
    assert self.is_fmla_type(Connective.NOT), \
            "FormulaProp.get_kid_node1(): not negation formula"
    return self.ast.children[0]

  def get_kid_node2(self) -> Tuple[Node, Node]:
    """ Get the kids of self, whose root is a binary connective. """
    root_token = self.ast.token
    assert root_token.value in CONN_LIST and root_token.arity ==2, \
            "FormulaProp.get_kid_node2(): not binary connective formula" 
    return (self.ast.children[0], self.ast.children[1])

  def verified_by(self, rule_inf: RuleInfer, premise: List[Node] = []) \
      -> bool: 
    """ Test if self is verified from (rule_inf, premise).
        If a subproof need be a member of premise, then use the formula 
        A imp B where A is the hypothesis and B is the last formula 
        of the subproof.
      """
    match rule_inf:
      case RuleInfer.BOT_INTRO:
        # return true iff self is bot and 
        # two premises are negations of each other
        if self.ast.token.value != 'bot' or len(premise) != 2:
          return  False
        not_i = 0 if premise[0].token.value == 'not' else 1
        not_prem = premise[not_i]
        other_prem = premise[1 - not_i]
        return not_prem.children[0] == other_prem
      case RuleInfer.BOT_ELIM:
        # return true iff the only premise is bot
        # self can be any formula
        return len(premise) == 1 and premise[0].token.value == 'bot'
      case RuleInfer.NOT_INTRO:
        # from the only premise A imp bot, infer not A
        if len(premise) != 1 or not self.is_fmla_type(Connective.NOT):
          return  False
        prem = FormulaProp(premise[0])
        if prem.is_fmla_type(Connective.IMP):
          left, right = prem.get_kid_node2()
          return left == self.get_kid_node1() and right.token.value == 'bot'
        else:
          return False
      case RuleInfer.NOT_ELIM:
        # from the only premise not A imp bot, infer A
        # This rule is usually called 'proof by contradiction' or
        # 'reductio ad absurdum' or double negation elimination,
        # and prohibited in inuitionistic logic.
        if len(premise) != 1:
          return  False
        prem = FormulaProp(premise[0])
        if prem.is_fmla_type(Connective.IMP):
          left, right = prem.get_kid_node2()
          left_fmla = FormulaProp(left)
          return left_fmla.is_fmla_type(Connective.NOT) and \
                 self.ast == left_fmla.get_kid_node1() and \
                 right.token.value == 'bot'
        else:
          return False
      case RuleInfer.AND_INTRO:
        # return true iff self is A and B
        # and the two premises are [A, B] or [B, A].
        if not self.is_fmla_type(Connective.AND) or len(premise) != 2:
          return  False
        left, right = self.get_kid_node2()
        return (premise[0] == left and premise[1] == right) or \
               (premise[0] == right and premise[1] == left)
      case RuleInfer.AND_ELIM:
        # return true iff prem is A and B and self is A or self is B
        if len(premise) != 1:
          return  False
        prem_fmla = FormulaProp(premise[0])
        left, right = prem_fmla.get_kid_node2()
        return (self.ast == left or self.ast == right) and \
                prem_fmla.is_fmla_type(Connective.AND)
      case RuleInfer.OR_INTRO:
        # from A, infer (A or B) or (B or A)
        if len(premise) != 1 or not self.is_fmla_type(Connective.OR):
          return  False
        left, right = self.get_kid_node2()
        return premise[0] == left or premise[0] == right
      case RuleInfer.OR_ELIM:
        pass
      case RuleInfer.IMP_INTRO:
        # from A imp B, infer A imp B
        # This rule looks silly because subproof premise must be 
        # converted to an implication formula
        return len(premise) == 1 and premise[0] == self.ast \
               and self.is_fmla_type(Connective.IMP)
      case RuleInfer.IMP_ELIM: # modus ponens
        if len(premise) != 2:
          return  False
        longer_i = 0 if premise[0].longer_than(premise[1]) else 1
        longer_prem = premise[longer_i]
        shorter_prem = premise[1 - longer_i]
        longer_fmla = FormulaProp(longer_prem)
        if longer_fmla.is_fmla_type(Connective.IMP):
          left, right = longer_fmla.get_kid_node2()
          if left == shorter_prem and right == self.ast:
            return True
        return False
      case RuleInfer.IFF_INTRO:
        # from (A imp B) and (B imp A), infer A iff B
        if len(premise) != 2 or not self.is_fmla_type(Connective.IFF):
          return False
        prem1_fmla = FormulaProp(premise[0])
        prem2_fmla = FormulaProp(premise[1])
        if prem1_fmla.is_fmla_type(Connective.IMP) and \
           prem2_fmla.is_fmla_type(Connective.IMP):
          left1, right1 = prem1_fmla.get_kid_node2()
          left2, right2 = prem2_fmla.get_kid_node2()
          left, right = self.get_kid_node2()
          return (left1 == right2 and right1 == left2) and \
                 ((left == left1 and right == right1) or \
                  (left == left2 and right == right2))
        else:
          return False
      case RuleInfer.IFF_ELIM:
        # from (A iff B) and A, infer B, and 
        # from (A iff B) and B, infer A
        if len(premise) != 2:
          return False
        longer_i = 0 if premise[0].longer_than(premise[1]) else 1
        longer_prem = premise[longer_i]
        shorter_prem = premise[1 - longer_i]
        longer_fmla = FormulaProp(longer_prem)
        if longer_fmla.is_fmla_type(Connective.IFF):
          left, right = longer_fmla.get_kid_node2()
          if (left == shorter_prem and right == self.ast) or \
             (right == shorter_prem and left == self.ast):
            return True
        return False
      case RuleInfer.REPEAT:
        # return true iff self is identical to the only premise
        return len(premise) == 1 and premise[0] == self.ast
      case RuleInfer.LEM:
        # return true iff self is of the form A or not A
        # and premise is empty
        if premise or not self.is_fmla_type(Connective.OR):
          return False
        kids = self.ast.children
        longer_i = 0 if kids[0].longer_than(kids[1]) else 1
        longer_kid = kids[longer_i]
        shorter_kid = kids[1 - longer_i]
        return longer_kid.token.value == 'not' and \
          longer_kid.children[0] == shorter_kid
      case RuleInfer.HYP:
        # We can assume any formula as a hypothesis
        # In other words, hypotheses do not need verification.
        return not premise
      case _:
        raise ValueError("FormulaProp.verified(): wrong rule_inf")
    return True # type checker needs this
  # end of class FormulaProp

class Ann: 
  """Annotation of a line of a proof tree"""
  def __init__(self, input_str: str):
    self.input_str = input_str
    self.rule = None # 'imp elim' | .. | 'ELM' 
    self.premise = None # [node_code,.. , ] 
                        # node_code ::= ln: int | (ln_s: int, ln_e: int)
                        # ln = line number
    self.parse()

  def __str__(self) -> str:
    if self.rule is None:
      return ''
    else:
      premise_str = ''
      if self.premise:
        for i, p in enumerate(self.premise):
          premise_str += ',' if i > 0 else ' '
          if isinstance(p, int):
            premise_str += f"{p}"
          else:
            premise_str += f"{p[0]}-{p[1]}"
      return f"{self.rule}{premise_str}"
    
  def build_str(self) -> str:
    if self.rule is None:
      return ''
    else:
      return (f"rule: {self.rule}\n" 
              f"premise: {str(self.premise)}")

  def parse(self) -> None:
    """From self.input_str, set self.rule and self.premise."""
    #region util functions
    def is_node_id(s: str) -> bool:
      """test if s is of the form '12' | '3-8'"""
      if Token.is_nat(s): # type: ignore
        return True
      else:
        s_li = s.split('-')
        if len(s_li) == 2 and \
            Token.is_nat(s_li[0]) and Token.is_nat(s_li[1]): # type: ignore
          return True
        else:
          return False
        
    def bFmla(s: str) -> bool:
      """test if s is a node id for a formula"""
      return Token.is_nat(s) # type: ignore
    
    def bSubproof(s: str) -> bool:
      """test if s is a node id for a subproof"""
      return is_node_id(s) and '-' in s
    
    def premise2int(num_s_li: List[str]) -> List[int | Tuple[int, int]]:
      """convert a list of node ids to a list of ints and 2-tuples of ints"""
      ret_li = []
      for num_s in num_s_li:
        pos = num_s.find('-')
        if pos == -1: # num_s is a node id for a formula
          ret_li.append(int(num_s))
        else: # num_s is a node id for a subproof
          ln_s = int(num_s[:pos])
          ln_e = int(num_s[pos+1:])
          ret_li.append((ln_s, ln_e))
      return ret_li
    #endregion util functions

    ann_s = self.input_str
    err_msg = f'Annotation string "{ann_s}" is not valid.'
    match = re.search(r'\d', ann_s) # find the 1st digit
    if match: # premise is nonempty
      pos = match.start()
      string_part = ann_s[:pos].strip()
      str_li = string_part.split() # e.g., ['imp', 'elim']
      num_part = ann_s[pos:]
      num_s_li = [num_s.strip() for num_s in num_part.split(',')]
      if not all([is_node_id(s) for s in num_s_li]):
        raise ValueError(err_msg + '\n\tWrong premise format.')
      if len(str_li) == 1:
        s0 = num_s_li[0]
        if str_li[0] == 'repeat' and len(num_s_li) == 1 and bFmla(s0):
          self.rule = 'repeat'
          self.premise = [int(s0)]
        else:
          raise ValueError("1: " + err_msg)
      elif len(str_li) == 2:
        conn = str_li[0]
        r_type = str_li[1] # rule type
        n_prem = len(num_s_li)
        if n_prem > 0:
          id1 = num_s_li[0]
        if n_prem > 1:
          id2 = num_s_li[1]
        if n_prem > 3 or n_prem == 0:
          raise ValueError(err_msg + "\n\tToo many or too few premises.")
        if conn in CONN_LIST and r_type in INTRO_ELIM:
          self.rule = conn + ' ' + r_type
          self.premise = premise2int(num_s_li) # tentatively
          bOK = True # tentatively
          if conn == 'bot': 
            if r_type == 'intro':
              bOK = n_prem == 2 and bFmla(id1) and bFmla(id2) # type: ignore
            else: # r_type == 'elim'
              bOK = n_prem == 1 and bFmla(id1) # type: ignore
          elif conn == 'neg':
            # intro or elim
            bOK = len(num_s_li) == 1 and bSubproof(id1) # type: ignore
          elif conn == 'and':
            if r_type == 'intro':
              bOK = n_prem == 2 and bFmla(id1) and bFmla(id2) # type: ignore
            else: # r_type == 'elim'
              bOK = n_prem == 1 and bFmla(id1) # type: ignore
          elif conn == 'or':
            if r_type == 'intro':
              bOK = n_prem == 1 and bFmla(id1) # type: ignore
            else: # r_type == 'elim'
              bOK = (n_prem == 3 and 
                     unique([bFmla(id) for id in num_s_li])) # type: ignore
          elif conn == 'imp':
            if r_type == 'intro':
              bOK = n_prem == 1 and bSubproof(id1) # type: ignore
            else: # r_type == 'elim'
              bOK = n_prem == 2 and bFmla(id1) and bFmla(id2) # type: ignore
          else: # conn == 'iff'
            if r_type == 'intro':
              bOK = n_prem == 2 and bSubproof(id1) and bSubproof(id2) # type: ignore
            else: # r_type == 'elim'
              bOK = n_prem == 2 and bFmla(id1) and bFmla(id2) # type: ignore
          if not bOK:
            raise ValueError('2: ' + err_msg)
          self.premise = premise2int(num_s_li)
        else:
          raise ValueError('3: ' + err_msg)
      else:
        raise ValueError(f'4: ' + err_msg)
    elif ann_s in ['LEM', 'hyp']: # the only case where premise is empty
      self.rule = ann_s
      self.premise = []
    else:
      raise ValueError('5: ' + err_msg)

  # end of class Annotation

class NodeLabel: 
  """label of a node of a proof tree (like a token)"""
  def __init__(self, type: str = 'subproof', line: str = '', 
               formula: Formula | None = None, ann: Ann | None = None):
    """ type ::= 'subproof' | 'formula' | 'comment' | 'blank'
        For subproofs, there's not much we need to do.
        The same is true for comments and blank lines.
        For formulas, initialization is done in two ways:
          (1) from a string, and 
          (2) from a Formula object and an Ann object.
    """
    self.type = type
    self.line = line
    self.formula = formula
    self.ann = ann
    self.is_hyp = None # type: bool | None
    self.node_code = None
    #^ node_code ::= ln: int | (ln_s: int, ln_e: int) | None
    #^ ln = line number, (ln_s, ln_e) is for subproofs
    if self.type != 'formula':
      pass
    elif self.line != '':
      self.parse_line()
    elif isinstance(formula, Formula) and isinstance(ann, Ann):
      self.is_hyp = ann.rule == 'hyp'
    else:
      raise ValueError("NodeLabel.init(): Wrong arguments")

  def parse_line(self) -> None:
    """ Parse self.line and set self.formula, self.ann and self.is_hyp.
        self.line does not have the line number part."""
    line = self.line
    # Isolate formula part and annotation part from line.
    pos = word_in_str(CONN_LIST + RULES_AUX, line)
    #^ line[pos] == '.' if pos != -1
    if pos == -1:
      pos = len(line)
    fmla_part = line[:pos].lstrip()
    ann_part = line[pos:].rstrip()
    if ann_part.startswith('.'):
      ann_part = ann_part[1:]
    else:
      ann_part = '' # actually, this is redundant
      #^ If fmla_part is illegal, then show error messages and exit.
    self.formula = Formula(parse_ast(fmla_part))
    # If ann_part is illegal, then set self.ann to ann_part.
    # So self.ann is either an Ann object or a string or None.
    try:
      self.ann = Ann(ann_part)
      self.is_hyp = self.ann.rule == 'hyp'
      # isinstance(self.ann, Ann)
    except Exception as e:
      # error, but keep it anyway
      # not isinstance(self.ann, Ann)
      self.ann = ann_part

  def __str__(self) -> str:
    if self.type == 'formula':
      return f"{self.formula}\t .{self.ann}"
    else: # self.type == 'subproof' | 'comment' | 'blank'
      return self.line
    
  def build_str(self) -> str:
    if self.type == 'subproof':
      return ''
    elif self.type == 'formula':
      return (f"type: {self.type}\n" 
              f"line: {self.line}\n"
              f"formula: {self.formula}\n"
              f"ann: {self.ann}\n"
              f"is_hyp: {self.is_hyp}")
    else:
      return self.line
    
  # end of class NodeLabel

class ProofNode: 
  def __init__(self, label: NodeLabel, children=None):
    self.label = label
    self.children = children if children else [] 
    #^ list of ProofNode objects, not the list of labels
    # The following 3 attributes are set by the build_index() method.
    self.index = None # type: List[int] | None
    self.line_num = None # type: str | None # e.g., '4', '6-10'
    self.index_dict = None # type: Dict[str, List[int]] | None

  def __str__(self) -> str:
    return self.build_fitch_text()
    
  def build_fitch_text(self) -> str:
    """ Recursively build Fitch-style proof text which looks like:
      │1. A imp B  .hyp
      │2. B imp C  .hyp
      ├─
      ││3. A   .hyp
      │├─
      ││4. B   .imp elim 1,3
      ││5. C   .imp elim 2,4
      │6. A imp C  .imp intro 3-5    
    """
    assert self.label.type == 'subproof', \
      "build_fitch_text(): this method must be called for a subproof"
    
    ret_str = ''
    b_hyp = True 
    level = len(self.index) if self.index else 0 # always >= 1
    for kid in self.children:
      if b_hyp and not kid.label.is_hyp:
        b_hyp = False
        ret_str += VERT * (level - 1) + '├─\n'
      if kid.label.type != 'subproof':
        line_str = f"{kid.label}"
        ret_str += VERT * level + f'{kid.line_num}. ' + line_str + '\n'
      else:
        ret_str += kid.build_fitch_text()
    return ret_str

  def build_fitch_latex(self) -> str:
    """ Build a Fitch-style proof latex source. """
    raise NotImplementedError("build_fitch_latex() not implemented")
  
  def build_index(self, p_index: List[int] = [], i: int = 0, 
                  l_num: int = 1) -> int:
    """ Recursively set self.index and self.line_num.
        Automatically called by the parse_fitch() function, where
        self is the root of the whole proof.

        p_index means the parent's (tree)index(: List[int]). 
        i is the (list)index(: int) of self in the parent's children list. 
        l_num is the line number to be given to self for leaf nodes.
        Return value is the increment of line number for the next leaf.
        self.index is recursively set from the root to the leaves.
        self.line_num is recursively set from the leaves to the root. 
    """
    self.index = p_index + [i]
    if self.children: # subproof case
      line_inc = 0 # tentative return value
      for i, kid in enumerate(self.children):
        line_inc += kid.build_index(self.index, i, l_num + line_inc)
      self.line_num = f"{l_num}-{l_num + line_inc - 1}"
    else: # leaf node case
      self.line_num = str(l_num)
      line_inc = 1

    return line_inc
  
  def build_index_dict(self) -> Dict[str, List[int]]:
    """ Recursively build a dictionary with line numbers as keys and 
        corresponding tree indices as values.
        Automatically called by the parse_fitch() function after build_index()
        has been called, where self is the root of the whole proof.
        The Return value is saved as proof_root.index_dict.
    """
    ret_dict = {}
    ret_dict[self.line_num] = self.index
    for kid in self.children:
      ret_dict.update(kid.build_index_dict())
    return ret_dict
    
  def get_node(self, node_code: List[int] | str):
    """ Get and return the node(: ProofNode) specified by node_code, which 
        is either a tree index(: List[int]) or a line number(:str).
        self must be the root of the whole proof. """
    assert self.index_dict is not None, "get_node(): index_dict is None"
    node = self
    if isinstance(node_code, str):
      index = self.index_dict.get(node_code)
      if index is not None:
        node = self.get_node(index) 
      else:
        raise ValueError(f"get_node(): line number {node_code} not found")
    else:
      if node_code == self.index:
        node = self
      else:
        for i in node_code[1:]:
          node = node.children[i]
    return node
  
  def toggle_node_code(self, node_code: List[int] | str) -> str | List[int]:
    """ Toggle node_code type between index and line number. """
    node = self.get_node(node_code)
    if node is None:
      raise ValueError("toggle_node_code(): node not found for " \
                       f"{node_code}")
    if isinstance(node_code, str):
      return node.index # type: ignore
    else:
      return node.line_num # type: ignore
    
  def is_earlier(self, node_code1, node_code2) -> bool:
    """ Test if node_code1 is earlier than node_code2, which is equivalent
        to saying that node_code1 can be used as a premise of node_code2. """
    assert self.index_dict is not None, "get_node(): index_dict is None"
    
    # make sure that both node_code1 and node_code2 are of the type List[int]
    node_code1 = node_code1 if not isinstance(node_code1, str) \
                  else self.index_dict[node_code1]
    node_code2 = node_code2 if not isinstance(node_code2, str) \
                  else self.index_dict[node_code2]
    
    # This order is somewhat unusual but very important.
    # It is at the heart of the Fitch proof system.    
    len1 = len(node_code1)
    return len1 <= len(node_code2) and \
           node_code1[:-1] == node_code2[:len1 - 1] and \
           node_code1[-1] < node_code2[len1 - 1]
  
  # end of class ProofNode

class ProofParser:
  def __init__(self, lines: List[str], tabsize: int):
    self.lines = lines
    self.current_line = None
    self.level = 1 # indentation level (ground level = 1)
    self.tabsize = tabsize
    self.index = -1
    self.advance()

  def advance(self): # increment self.index and set self.current_line
    self.index += 1
    if self.index < len(self.lines):
      self.current_line = self.lines[self.index]
    else:
      self.current_line = None
       
  def proof(self) -> ProofNode:
    children = []
    while (line_str := self.current_line) is not None:
      if line_str == '{{':
        self.level += 1
        self.advance()
        children.append(self.proof())
      else:
        if line_str == '}}':
          self.level -= 1
          if self.level <= 0:
            raise ValueError("ProofParser.proof(): below ground level")
          self.advance()
          break
        elif line_str == '':
          label_type = 'blank'
        elif line_str.lstrip().startswith('#'):
          label_type = 'comment'
        else:
          label_type = 'formula'
        label = NodeLabel(label_type, line_str)
        children.append(ProofNode(label)) # leaf node
        self.advance()

    return ProofNode(NodeLabel(), children)
  
  # end of class ProofParser

def parse_fitch(proof_str: str, tabsize: int = 2) -> ProofNode:  
  lines = get_str_li(proof_str, tabsize) 
  #^ list of strings, where the subproofs are indicated by double brace pairs
  #^ each element of the list corresponds to a line of the proof
  parser = ProofParser(lines, tabsize)
  proof_node = parser.proof()
  proof_node.build_index()
  proof_node.index_dict = proof_node.build_index_dict()
  if parser.level != 1:
    raise ValueError("parse_fitch(): parsing ended with non-ground level")
  return proof_node

#region util functions
def ge_n(li: List[bool], n: int) -> bool:
  # test if there are at least n True in li
  count = 0
  for i in li:
    if i:
      count += 1
      if count >= n:
        return True
  return False

def exists(li: List[bool]) -> bool:
  # test if there is at least one True in li
  # the same as any(li)
  return ge_n(li, 1)

def ge2(li: List[bool]) -> bool:
  # test if there are at least 2 True in li
  return ge_n(li, 2)

def eq_n(li: List[bool], n: int) -> bool:
  # test if there are exactly n True in li
  count = 0
  for i in li:
    if i:
      count += 1
      if count > n:
        return False
  return count == n

def unique(li: List[bool]) -> bool:
  # test if there is only one True in li
  return eq_n(li, 1)

def word_in_str(word_li: List[str], text: str) -> int:
  # Test if there exists a word in word_li occurring in text.
  # If negative, return -1.
  # If positive, return the index of the first occurrence of the 
  # word in word_li.
  import re

  word_li_dot = [r"\." + word for word in word_li]
  my_re = r"\b" +'|'.join(word_li_dot) + r"\b"
  m = re.search(my_re, text)
  if m is None:
    return -1
  else:
    s = m.start()
    e = m.end()
    if (s == 0 or text[s-1] in [' ', '\t']) and \
       (e == len(text) or text[e] in [' ', '\t']):
      return s
    else:
      return -1

def get_str_li(proof_str: str, tabsize: int) -> List[str]:
  """
  This is a preprocessing function for parse_fitch().

  Convert proof_str to a list of strings, where the subproofs are
  indicated by double brace pairs.

  Indentation is the key to parsing a Fitch-style proof.
  In proof_str, indentations are indicated by tabs or spaces or VERTs.
  1. For each line, get the level from the number of leading spaces 
    or TABs or VERTs 
  2. Remove the leading line number if any from each line.
  3. From the change of level between lines, convert indentation to 
    double brace pairs to indicate subproofs.
  4. When there is a change of line type from conclusion to hyp, add
    ["}}", "{{"] to the list.
  """
  # split proof_str into lines
  str_li = proof_str.split('\n') # this will be converted to str_li_ret
  # remove leading and trailing empty line if any
  if len(str_li[0]) == 0 or str_li[0].isspace():
    str_li = str_li[1:]
  if len(str_li[-1]) == 0 or str_li[-1].isspace():
    str_li = str_li[:-1]

  # determine whether VERT was used for indentation
  VERT_used = str_li[0].startswith(VERT)

  str_li_ret = [] # this will be returned
  TAB_sp = ' ' * tabsize
  pat_num = re.compile(r'\d+\.\s*') # for matching line numbers
  pat_hyp = re.compile(r'\s+\.hyp$') # for matching hypotheses
  level0 = 1
  is_conclusion = False
  proves_str = PROVES if VERT_used else 'proves'
  for str in str_li:
    if VERT_used:
      level = 0
      while str.startswith(VERT):
        str = str[1:]
        level += 1
    else:
      level = 1
      while True:
        if str.startswith(TAB):
          str = str[1:]
          level += 1
        elif str.startswith(TAB_sp):
          str = str[tabsize:]
          level += 1
        else:
          break
    if (m := pat_num.search(str)):
      str = str[m.end():] # remove leading line number if any
    if str.find(proves_str) == -1:
      if level > level0:
        str_li_ret.append("{{")
      elif level < level0:
        while level < level0:
          str_li_ret.append("}}")
          level0 -= 1
      else: # level == level0 case
        # If the previous line is a conclusion and the current line
        # is a hypothesis, then add ["}}", "{{"].
        if is_conclusion:
          if pat_hyp.search(str):
            str_li_ret += ["}}","{{"]
            is_conclusion = False
        else: # is_hyp
          if not pat_hyp.search(str):
            is_conclusion = True
      str_li_ret.append(str)
      level0 = level
    else: # proves_str is ignored
      pass

  return str_li_ret

def print_lines(lines: List[str]) -> None:
  """ This is a test driver function for get_str_li().
      Print lines with indentation. """
  level = 1
  for str in lines:
    if str == "}}":
      print(f"{('  ' * (level - 2))}{str}")
      level -= 1
    else:
      print(f"{('  ' * (level - 1))}{str}")
    if str == "{{":
      level += 1
#endregion util functions
