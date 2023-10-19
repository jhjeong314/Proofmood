#region 0 
from typing import List, Tuple, Dict, Set, Any, NewType
import re
from enum import Enum

# Make colorama module available.
import sys, subprocess
try:
  from colorama import Fore, Back, Style
except ModuleNotFoundError:
  subprocess.check_call(
    [sys.executable, '-m', 'pip', 'install', 'colorama'],
      stdout=subprocess.DEVNULL
  )
  print("colorama installed")
  from colorama import Fore, Back, Style

from modules.truth_table import * 

class RuleInfer(Enum):
  # ordered by the precedence of proof search 
  LEM = "LEM"
  REPEAT = "repeat"
  BOT_INTRO = "bot intro"
  NOT_INTRO = "not intro"
  AND_INTRO = "and intro"
  OR_INTRO = "or intro"
  IMP_INTRO = "imp intro"
  IFF_INTRO = "iff intro"
  BOT_ELIM = "bot elim"
  NOT_ELIM = "not elim"
  IMP_ELIM = "imp elim"
  IFF_ELIM = "iff elim"
  AND_ELIM = "and elim"
  OR_ELIM = "or elim"
  HYP = "hyp" # not a real rule of inference but necessary for
              # determining whether a line is in hypothesis or not

tree_index = NewType("t_node", List[int]) # tree index (e.g., [1, 0, 2])
n_code = NewType("n_code", str) # node code (e.g., '1', '2-3')

CONN_LIST = [conn.value for conn in Connective]
INTRO_OR_ELIM = ['intro', 'elim']
RULES_AUX = ['repeat', 'LEM', 'hyp']
VERT = '│'
PROVES = '├─'
TAB = '\t'
#endregion 0

class FormulaProp(Formula):
  def __init__(self, input: str | Node):
        super().__init__(input)
  
  def get_kid_node1(self) -> Node:
    """ Get the kid node of self, which is a negation formula. """
    assert self.is_fmla_type(Connective.NOT), \
            "FormulaProp.get_kid_node1(): not negation formula"
    return self.ast.children[0]

  def get_kid_node2(self) -> Tuple[Node, Node]:
    """ Get the kids of self, whose root is a binary connective. """
    root_token = self.ast.token
    assert (v := root_token.value) in CONN_LIST and root_token.arity ==2, \
            f"FormulaProp.get_kid_node2(): '{v}' is not binary connective"
    return (self.ast.children[0], self.ast.children[1])

  def verified_by(self, rule_inf: RuleInfer, premise: List[Node] = []) \
      -> bool: 
    """ Test if self is verified by (rule_inf, premise).
        If a subproof need be a member of premise, then we must use 
        the formula A imp B instead where A is the hypothesis and B 
        is the last formula of the subproof.
      """
    match rule_inf:
      case RuleInfer.BOT_INTRO:
        # return true iff self is bot and 
        # two premises are negations of each other
        if self.ast.token.value != 'bot' or len(premise) != 2:
          return  False
        not_i = 0 if premise[0].token.value == 'not' else 1
        not_prem = premise[not_i]
        if not FormulaProp(not_prem).is_fmla_type(Connective.NOT):
          return False
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
        if not prem_fmla.is_fmla_type(Connective.AND):
          return False
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
        if len(premise) != 3: # the only rule with 3 premises
          return False
        for i in range(3):
          or_fmla = FormulaProp(premise[i])
          if or_fmla.is_fmla_type(Connective.OR):
            break
        else:
          return False
        imp_fmla1 = FormulaProp(premise[(i+1) % 3])
        imp_fmla2 = FormulaProp(premise[(i+2) % 3])
        if not (imp_fmla1.is_fmla_type(Connective.IMP) and \
                imp_fmla2.is_fmla_type(Connective.IMP)):
          return False
        left, right = or_fmla.get_kid_node2()
        left1, right1 = imp_fmla1.get_kid_node2()
        left2, right2 = imp_fmla2.get_kid_node2()
        if right1 != right2 or right1 != self.ast:
          return False
        return (left == left1 and right == left2) or \
          (left == left2 and right == left1)
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
        # We can assume any formula as a hypothesis.
        # In other words, hypotheses do not need verification.
        return not premise
      case _:
        raise ValueError(f"Rule {rule_inf} is not supported.")
  
  # end of class FormulaProp

class Ann: 
  """Annotation of a line of a proof tree"""
  def __init__(self, input_str: str=''):
    # Caution: NodeLabel.ann is either an Ann object or a string or None.
    #   When parsing NodeLabel fails because annotation string is invalid, 
    #   then label.ann becomes a string via exception handling.
    self.input_str = input_str
    self.rule = None # RuleInfer type
    self.premise = None # [node_code,.. , ] 
                        # node_code ::= ln: digit | ln_s-ln_e: str
                        # ln = line number
    self.parse()

  def __str__(self) -> str:
    if self.rule is None:
      return ''
    else:
      premise_str = ','.join(self.premise) if self.premise else ''
      return f"{self.rule.value} {premise_str}"
    
  def build_str(self) -> str:
    if self.rule is None:
      return ''
    else:
      return (f"rule: {self.rule.value}\n" 
              f"premise: {self.premise}")

  rules_prem2 = ['bot intro', 'and intro', 'imp elim', 
                 'iff intro', 'iff elim']
  rules_prem3 = ['or elim']

  def parse(self) -> None:
    """From self.input_str, set self.rule and self.premise."""
    ann_s = self.input_str.strip()
    if not ann_s: # return the empty annotation
      self.input_str = ann_s
      return
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
        if str_li[0] == 'repeat' and len(num_s_li) == 1 and bLeafNode(s0):
          self.rule = RuleInfer.REPEAT
          self.premise = [s0]
        else:
          raise ValueError("1: " + err_msg)
      elif len(str_li) == 2:
        conn = str_li[0]
        r_type = str_li[1] # rule type ::= 'intro' | 'elim'
        rule_inf_str = conn + ' ' + r_type
        n_prem = len(num_s_li)
        if n_prem > 0:
          id1 = num_s_li[0]
        if n_prem > 3 or n_prem == 0:
          raise ValueError(err_msg + "\n\tToo many or too few premises.")
        if conn in CONN_LIST and r_type in INTRO_OR_ELIM:
          self.rule = RuleInfer(rule_inf_str)
          self.premise = num_s_li
          bOK = True # tentatively
          if rule_inf_str in Ann.rules_prem2:
            bOK = n_prem == 2
          elif rule_inf_str in Ann.rules_prem3:
            bOK = n_prem == 3
          elif rule_inf_str in ('imp intro', 'not intro', 'not elim'):
            bOK = n_prem == 1 and bSubproof(id1)
          else:
            bOK = n_prem == 1
          if not bOK:
            raise ValueError('2: ' + err_msg)
          # self.premise = num_s_li
        else:
          raise ValueError('3: ' + err_msg)
      else:
        raise ValueError(f'4: ' + err_msg)
    elif ann_s in ['LEM', 'hyp']: # the only case where premise is empty
      self.rule = RuleInfer(ann_s)
      self.premise = []
    else:
      raise ValueError('5: ' + err_msg)

  # end of class Annotation

class NodeLabel: 
  """label of a node of a proof tree (like a token)"""
  def __init__(self, type: str = 'subproof', line: str = '', 
               formula: Formula | None = None, ann: Ann | None = None):
    """ type ::= 'subproof' | 'formula' | 
          'comment.hypo' | 'blank.hypo' | 'comment.conc' | 'blank.conc'
        For subproofs, there's not much we need to do.
        For comments and blank lines, we only need to set self.is_hyp,
          to indicate whether the line is in hypothesis or conclusion.
        For formulas, initialization is done in two ways:
          (1) from a string, and 
          (2) from a Formula object and an Ann object.
    """
    self.type = type
    self.line = line
    self.formula = formula
    self.ann = ann
    self.is_hyp = None # type: bool | None
    if self.type != 'formula':
      self.is_hyp = self.type.endswith('.hypo')
    elif self.line != '':
      self.parse_line()
    elif isinstance(formula, Formula) and isinstance(ann, Ann):
      self.is_hyp = ann.rule == RuleInfer.HYP
    else:
      raise ValueError("NodeLabel.init(): Wrong arguments for formula type.")

  def parse_line(self) -> None:
    """ Parse self.line and set self.formula, self.ann and self.is_hyp.
        self.line does not have the line number part."""
    line = self.line
    # Isolate formula part and annotation part from line.
    pos = word_in_str(CONN_LIST + RULES_AUX, line)
    #^ line[pos] == '.' if pos != -1
    if pos == -1:
      pos = len(line)
    else:
      dot_exists = True
    fmla_part = line[:pos].lstrip()
    if fmla_part == '':
      # empty formula is treated as 'top' which is always True
      fmla_part = 'top' 
    ann_part = line[pos:].rstrip()
    if ann_part.startswith('.'):
      ann_part = ann_part[1:]
    else:
      if ann_part == '' and fmla_part.find(".") != -1:
        # It is ok to have empty annotation for a line. But
        # if there is a dot in the formula part, then it is very likely
        # that there is an error. E.g., 
        raise ValueError(f"parse_line(): line = '{line}'\n" 
            "\tAnnotation part is missing.\n"
            "\tPerhaps there is a typo in the rule of inference.")
      #^ If fmla_part is illegal, then show error messages and exit.
    self.formula = Formula(parse_ast(fmla_part))
    # If ann_part is illegal, then set self.ann to ann_part.
    # So self.ann is either an Ann object or a string or None.
    try:
      self.ann = Ann(ann_part)
      self.is_hyp = (self.ann.rule == RuleInfer.HYP)
    except Exception as e:
      # Error: not isinstance(self.ann, Ann)
      # keep it for debugging purpose
      # It's easy to spot the error anyway because 
      # it'll appear in red in the output.
      self.ann = ann_part

  def __str__(self) -> str:
    if self.type == 'formula':
      return f"{self.formula}\t .{self.ann}"
    else: # self.type == 'subproof' | 'comment.*' | 'blank.*'
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
  # In order to get node: Node from p_node: ProofNode, first check
  #   p_node.label.type == 'formula', and then let
  #   node = p_node.label.formula.ast
  # Of course this is possible iff p_node.label.type == 'formula'.
  # Each and every line and subproof of a Fitch proof has a 
  # corresponding ProofNode object.
  def __init__(self, label: NodeLabel, children=None):
    self.label = label
    self.children = children if children else [] 
    #^ list of ProofNode objects, not the list of labels
    # The following 2 attributes are set by the build_index() method.
    self.index = None # type: List[int] | None
    self.line_num = None # type: str | None # e.g., '4', '6-10'
    # The 4th attribute is set within the parse_fitch() function
    # using the build_index_dict() method.
    self.index_dict = None # type: Dict[str, List[int]] | None
    # The last attribute is set within the parse_fitch() function
    # using the verified() method.
    self.validated = None # type: bool | None

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
      # When the line changes from hyp to non-hyp, insert '├─\n'.
      if b_hyp and not kid.label.is_hyp:
        b_hyp = False
        ret_str += VERT * (level - 1) + '├─\n'
      # Output the line for leaf nodes only.
      if kid.label.type != 'subproof': # output for leaf node 
        line_str = f"{kid.label}"
        ret_str += VERT * level + f'{kid.line_num}. ' + line_str + '\n'
      else: # recursively call build_fitch_text() for subproofs
        ret_str += kid.build_fitch_text()
    return ret_str

  def show_fitch_text(self, verbose: bool = True) -> None:
    """ If verbose is False, then simply print the return value of 
        build_fitch_text(). Otherwise, show whether each line passed
        validation or not by colored marks, i.e.,
        check mark for success and x-mark for failure. 
        We allow verbose to be an integer so that we can use 1  
        in place of True.
    """
    text_str = self.build_fitch_text()
    #^ Each line in text_str has been treated so that 
    #  left border uses VERT and line numbers exist etc.
    if not verbose:
      print(text_str) # trivial
    else:
      # Show whether each line is validated or not by colored marks.
      # Of course this is for formula line only.
      b_hyp = True
      level = len(self.index) if self.index else 0 # always >= 1
      for kid in self.children:
        # When the line changes from hyp to non-hyp, insert '├─\n'.
        if b_hyp and not kid.label.is_hyp:
          b_hyp = False
          print(VERT * (level - 1) + '├─')
        # Output the line for leaf nodes only.
        if kid.label.type != 'subproof':
          print(VERT * level, sep="", end="")
          print(f"{kid.line_num}. ", sep="", end="")
          # Now, we print the line with colored marks for formula lines.
          # Comment/blank lines are relatively easy to handle.
          label = kid.label
          if label.type == 'formula':
            fmla_str = f"{label.formula}"
            if not label.is_hyp: # formula line in conclusion
              if isinstance(label.ann, Ann):
                print(fmla_str, end="")
                if kid.validated:
                  print("\t", Fore.LIGHTGREEN_EX, '\u2713', Fore.RESET, sep="", end="")
                else:
                  print("\t", Fore.LIGHTRED_EX, 'x', Fore.RESET, sep="", end="")
                print(f" {label.ann}")
              else:
                print(fmla_str, end="")
                print("\t", Fore.LIGHTRED_EX, 'x', f" {label.ann}", Fore.RESET, sep="")
            else: # hypothesis
              # 'top' is empty formula
              fmla_str = '' if fmla_str == 'top' else fmla_str
              print(f"{fmla_str}\t .hyp")
          else: # comment or blank line
            print(f"{label}")
        else:
          kid.show_fitch_text(verbose)       

  def build_fitch_latex(self, verbose: bool = True) -> str:
    """ Build a Fitch-style proof latex source. 
        Need proofmood.sty for compilation. """
    def build_fitch_latex_rec(node: ProofNode) -> str:
      ret_str = ''
      b_hyp = True
      level = len(node.index) if node.index else 0 # always >= 1
      for kid in node.children:
        # When the line changes from hyp to non-hyp, insert '├─\n'.
        if b_hyp and not kid.label.is_hyp:
          b_hyp = False
          ret_str += "& " +  "\\pmvert " * (level - 1) + "\\pmproves & & & \\\\\n"
        # Output the line for leaf nodes only.
        label = kid.label
        if label.type != 'subproof': # subproof is internal node
          line_num = "\\pnumb{" + f'{kid.line_num}'+ "} "
          if label.type == 'formula':
            vert = "& " + "\\pmvert " * level
            fmla = "\\pform{" + label.formula.ast.build_infix('latex') + "} "
            if verbose and not kid.label.is_hyp:
              check = '& \\chkch ' if kid.validated else '& \\chkx '
            else:
              check = "& \\chknull "
            # Annotation part
            if isinstance(label.ann, Ann) and label.ann.rule : 
              # successfully parsed
              rule_li = label.ann.rule.value.split() # type: ignore
              rule_name = rule_li[0]
              if len(rule_li) == 1:
                rule_inf = "& \\infrul{" + rule_name + "} "
              else:
                assert rule_name in Node.LATEX_DICT
                rule_latex = Node.LATEX_DICT.get(rule_name)
                intro_elim = rule_li[1]
                rule_inf = "& \\infrule{" + rule_latex + "}{" + intro_elim + "}" # type: ignore
              if label.ann.premise:
                prem = "& \\pmprem{" + ",".join(label.ann.premise) + "} "
              else:
                prem = "& "
            else: # failed to parse or empty annotation. 
              # if failed to parse, then label.ann is a string.
              if isinstance(label.ann, str):
                ann_str = "\\; ".join(label.ann.split())
              else:
                ann_str = ''
              rule_inf = "&  \\multicolumn{2}{l}{" + "\\infruleErr{" + \
                ann_str + "}} "
              prem = ""
            nl = "\\pmnl\n"
            ret_str +=  vert + line_num + fmla + check + rule_inf + prem + nl
          else: # label.type == 'comment.*' | 'blank.*' where * ::= 'hypo' | 'conc'
            word_li = kid.label.line.replace("#", "\\#").split()
            line_str = "\\infrul{" + "\\; ".join(word_li) + "}"
            vert = "\\pmvert " * level
            ret_str += "& \\multicolumn{4}{l}{" + vert + line_num + line_str + \
                       "} " + "\\pmnl\n"
        else: # recursively call build_fitch_latex_rec() for subproofs
          ret_str += build_fitch_latex_rec(kid)
          ret_str += "& " +  "\\pmvert " * level + "& & & \\\\\n"
      return ret_str

    ret_str = "% \\usepackage{proofmood}\n" + \
              "\\begin{fitchproof}\n"
    ret_str += build_fitch_latex_rec(self)
    ret_str += "\\end{fitchproof}\n"
    return ret_str
  
  def build_index(self, p_index: List[int] = [], i: int = 0, 
                  l_num: int = 1) -> int:
    """ Recursively set self.index and self.line_num.
        Automatically called by the parse_fitch() function, where
        self is the root of the entire proof.

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
    
  def get_p_node(self, node_code: List[int] | str): # ProofNode type
    """ Get and return the p_node specified by node_code, which 
        is either a tree index(: List[int]) or a line number(:str).
        node_code of the form 's-e' is accepted too.
        self must be the root of the whole proof. """
    assert self.index_dict is not None, "get_p_node(): index_dict is None"
    p_node = self
    if isinstance(node_code, str):
      index = self.index_dict.get(node_code)
      if index is not None:
        p_node = self.get_p_node(index) 
      else:
        raise ValueError(f"get_p_node(): line number {node_code} not found")
    else:
      if node_code == self.index:
        p_node = self
      else:
        for i in node_code[1:]:
          p_node = p_node.children[i]
    return p_node 
  
  def toggle_node_code(self, node_code: List[int] | str) -> str | List[int]:
    """ Toggle node_code type between index and line number. """
    node = self.get_p_node(node_code)
    if node is None:
      raise ValueError("toggle_node_code(): node not found for " \
                       f"{node_code}")
    if isinstance(node_code, str):
      return node.index # type: ignore
    else:
      return node.line_num # type: ignore

  def is_earlier(self, node_code1, node_code2) -> bool:
    """
    Check if node_code1 precedes node_code2. This implies that node_code1
    can serve as a premise for node_code2, with the condition that
    node_code1 cannot be a direct ancestor of node_code2.

    is_earlier() is a partial order, and that's it. In order for 
    node_code2 can use node_code1 as a premise, node_code2 must be
    of formula type and not hyp.
    """
    assert self.index_dict is not None, "get_p_node(): index_dict is None"
    
    # make sure that both node_code1 and node_code2 are of the type List[int]
    ncode1 = node_code1
    ncode2 = node_code2
    node_code1 = node_code1 if not isinstance(node_code1, str) \
                  else self.index_dict.get(node_code1)
    if node_code1 is None:
      print("is_earlier(): node_code=", Fore.YELLOW, f"{ncode1}",
             Fore.RESET, " not found in index_dict\n", sep="")
      return False
    node_code2 = node_code2 if not isinstance(node_code2, str) \
                  else self.index_dict.get(node_code2)
    if node_code2 is None:
      print("is_earlier(): node_code=", Fore.YELLOW, f"{ncode2}",
             Fore.RESET, " not found in index_dict\n", sep="")
      return False
    
    # This order is somewhat unusual but very important.
    # It is at the heart of the Fitch proof system.    
    len1 = len(node_code1)
    return len1 <= len(node_code2) and \
           node_code1[:-1] == node_code2[:len1 - 1] and \
           node_code1[-1] < node_code2[len1 - 1]
  
  def verified_by(self, conc: str | int, rule_inf: RuleInfer, 
                  premise: List[str] = []) -> bool:
    """ Test if the conclusion with line number conc is verified by 
        (rule_inf, premise). conc of the form 's-e' is not accepted.
        self must be the root of the whole proof. """
    conc = str(conc) # type coercion
    assert bLeafNode(conc), f"verified_by(): line {conc} is not conclusion"
    assert self.index_dict is not None, "verified_by(): index_dict is None"
    p_node = self.get_p_node(conc) # ProofNode type
    assert p_node.label.type == 'formula', \
      f"verified_by(): conclusion='{conc}' is not a formula"
    if p_node.label.is_hyp:
      return True
    else:
      fmla = p_node.label.formula
      conclusion = FormulaProp(fmla.ast) # type: ignore
      premise_nodes = []
      for ln_num in premise:
        if not self.is_earlier(ln_num, conc):
          return False
        if bLeafNode(ln_num):
          label = self.get_p_node(ln_num).label
          if label.type != 'formula':
            # comment or blank line cannot be a premise
            return False
          else:
            fmla = self.get_p_node(ln_num).label.formula
          if fmla is None:
            raise ValueError("verified_by(): fmla is None for "
                             f"ln_num={ln_num}")
          premise_nodes.append(fmla.ast) # type: ignore
        else: # ln_num is subproof. Convert it to implication formula.
          node = self.subproof2implication(ln_num)
          premise_nodes.append(node)
      return conclusion.verified_by(rule_inf, premise_nodes)

  def subproof2implication(self, line_num: str) -> Node:
    str_li = [str.strip() for str in line_num.split('-')]
    s = str_li[0] # start line number
    e = str_li[1] # end line number
    # If s or e is not a formula (i.e., comment or blank line)
    # then we look for the next one. 
    # s increases until it is formula as long as it is hyp.
    # e decrease until it is formula as long as it is conc and leaf.
    while True:
      label = self.get_p_node(s).label
      if not label.is_hyp:
        raise ValueError(f"verified_by(): s={s} is not a hypothesis")
      if label.type == 'formula':
        break; 
      s = str(int(s) + 1)
    node_s = label.formula.ast # type: ignore
    while int(e) > 0:
      label = self.get_p_node(e).label
      if label.is_hyp or label.type == 'subproof':
        raise ValueError(f"verified_by(): e='{e}' is hyp or subproof")
      if label.type == 'formula':
        break; 
      e = str(int(e) - 1) # loop when e is a comment or a blank line
    else:
      raise ValueError("verified_by(): failed to find the conclusion" \
                        f" of '{s}-{e}'")
    node_e = label.formula.ast # type: ignore
    conn = Token("imp")
    return Node(conn, [node_s, node_e])

  def verified(self, conc: str | int) -> bool:
    """ Test if the conclusion with line number conc is verified 
        by its annotation.  conc of the form 's-e' is not accepted.
        self must be the root of the whole proof. 
    """
    conc = str(conc) # type coercion
    assert bLeafNode(conc), f"verified(): line {conc} is not conclusion"
    assert self.index_dict is not None, "verified_by(): index_dict is None"
    p_node = self.get_p_node(conc) # ProofNode type
    ann = p_node.label.ann
    if not isinstance(ann, Ann) or not ann.rule:
      return False
    else:
      return self.verified_by(conc, ann.rule, ann.premise) # type: ignore
    
  def verified_all(self) -> bool:
    """ Test if all conclusions are verified by their annotations.
        self must be the root of the whole proof. """
    assert self.index_dict is not None, "verified_by(): index_dict is None"
    for node_code in self.index_dict:
      if bSubproof(node_code):
        continue
      p_node = self.get_p_node(node_code) # ProofNode type
      if (label := p_node.label).type == 'formula':
        if label.is_hyp:
          continue
        if self.verified(node_code):
          continue
        else:
          return False
    return True

  def show_validation_result(self):  
    if self.verified_all():
      print("The proof is", Fore.LIGHTGREEN_EX, 
            " all valid", Fore.RESET, ".\n", sep='')
    else:
      print("The proof is", Fore.LIGHTRED_EX, 
            " invalid", Fore.RESET, ".\n", sep='')

  def validate_all(self) -> None:
    # set the p_node.validated attribute of each node
    for node_code in self.index_dict: 
      if bSubproof(node_code):
        continue
      p_node = self.get_p_node(node_code)
      if (label := p_node.label).type == 'formula' and not label.is_hyp:
        p_node.validated = self.verified(node_code)
      else: # hyp, comment, blank are all considered as validated
        p_node.validated = True 

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
    # The return value of this method can be illegitimate.
    # Integrity is checked later in the parse_fitch() function.

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
        if (is_hypo:=line_str.endswith('.hypo_')) or line_str.endswith('.conc_'):
          #^ comment or blank line case
          line_str = line_str[:-6]
          suffix = '.hypo' if is_hypo else '.conc'
          if line_str == '' or line_str.isspace():
            label_type = 'blank' + suffix
          elif line_str.lstrip().startswith('#'):
            label_type = 'comment' + suffix
          else:
            raise ValueError("ProofParser.proof(): .hypo_ .conc_ error")
        else: # formula case
          label_type = 'formula'
        label = NodeLabel(label_type, line_str)
        children.append(ProofNode(label)) # leaf node
        self.advance()

    return ProofNode(NodeLabel(), children)
  
  # end of class ProofParser

def parse_fitch(proof_str: str, validate=True, tabsize: int = 2) \
              -> ProofNode:  
  lines = get_str_li(proof_str, tabsize) 
  #^ List of strings, where the subproofs are indicated by double brace pairs.
  #^ Each element of the list corresponds to a line of the proof.
  parser = ProofParser(lines, tabsize)
  proof_node = parser.proof() # proof_node is a ProofNode object
  if parser.level != 1: # just give warning
    print("parse_fitch(): parsing ended with " + 
          Fore.YELLOW, "non-ground level\n" + Fore.RESET, sep="")
  proof_node.build_index()
  proof_node.index_dict = proof_node.build_index_dict()
  # Check that in all subproofs, the hypothesis have at least one line
  # and at most one formula.
  for node_code in proof_node.index_dict:
    if bSubproof(node_code) and node_code[:1] != '1':
      p_node = proof_node.get_p_node(node_code)
      hyp_list = [kid for kid in p_node.children if kid.label.is_hyp]
      if len(hyp_list) == 0:
        raise ValueError("parse_fitch(): "
                         f"subproof '{node_code}' has no hypothesis")
      if len([kid for kid in hyp_list if kid.label.type=='formula']) > 1:
        raise ValueError(f"parse_fitch(): subproof '{node_code}'" 
                         " has more than one hypothesis formula")
  if validate:
    # set the p_node.validated attribute of each node
    proof_node.validate_all()

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

def num_nodes(tree, opt='terminal') -> int:
  # opt!='terminal' means count terminal nodes only
  num = 0 if opt == 'terminal' else 1
  for kid in tree.children:
    if kid.children:
      num += num_nodes(kid, opt)
    else:
      num += 1
  return num

def word_in_str(word_li: List[str], text: str) -> int:
  # Test if there exists a member of word_li occurring in text.
  # If negative, return -1.
  # If positive, return the index of the first occurrence of the 
  # word in word_li.
  import re

  word_li_dot = [r"\." + word for word in word_li]
  my_re = r"(?<![\w])" +'|'.join(word_li_dot) + r"\b"
  #^ r"(?<![\w])" is used to match 
  #   \b followed by a dot followed by .bot, .hyp etc.
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

def get_str_li(proof_str: str, tabsize: int, verbose: bool = False) \
              -> List[str]:
  """
  This is a preprocessing function for parse_fitch().

  Convert proof_str to a list of strings, where the subproofs are
  indicated by double brace pairs.

  verbose is for debugging purpose. If True, then print the result.

  Indentation is the key to parsing a Fitch-style proof.
  In proof_str, indentations are indicated by tabs or spaces or VERTs.
  1. For each line, get the level from the number of leading spaces 
    or TABs or VERTs 
  2. Remove the leading line number if any from each line.
  3. From the change of level between lines, convert indentation to 
    double brace pairs to indicate subproofs.
  4. When there is a change of line type from conclusion to hyp in the
    same level, add ["}}", "{{"] to the list.

  Indentation is important for blank lines and comments too. So we
  must be very careful about them. Some editors may automatically
  remove white spaces of blank lines. So it may be a good idea to prefix
  a # character to each blank line.
  """
  # split proof_str into lines
  str_li = proof_str.split('\n') # this will be converted to str_li_ret
  # remove leading and trailing empty line if any
  if len(str_li[0]) == 0 or str_li[0].isspace():
    str_li = str_li[1:]
  if len(str_li[-1]) == 0 or str_li[-1].isspace():
    str_li = str_li[:-1]
  # Remove trailing spaces from each line if the line has at least one
  # nonwhite character. Leading spaces is not removed because
  # they are used for indentation.
  str_li = [str if str.isspace() else str.rstrip() for str in str_li]
  
  # determine whether VERT was used for indentation
  VERT_used = str_li[0].startswith(VERT)

  str_li_ret = [] # this will be returned
  TAB_sp = ' ' * tabsize
  pat_num = re.compile(r'^\s*\d+\.\s*') # for matching line numbers
  pat_hyp = re.compile(r'\s*\.hyp$') # for matching hypotheses
  pat_hyp_false = re.compile(r'\.\s+hyp$') # false pattern for hyp
  level0 = 1
  proves_str = PROVES if VERT_used else 'proves'
  belongs_to_hyp = True # current line is before the proves_str
  # Use the following bool variable to prevent empty conclusion part
  right_after_proves = False 
  for str in str_li:
    # get the level of the current line, and
    # remove the indentation part from the current line
    if VERT_used:
      level = 0
      while str.startswith(VERT):
        str = str[1:]
        level += 1
    else:
      level = 1 # reset and start fresh
      while True:
        if str.startswith(TAB):
          str = str[1:]
          level += 1
        elif str.startswith(TAB_sp):
          str = str[tabsize:]
          level += 1
        else:
          break
    # remove leading line number if any
    if (m := pat_num.search(str)):
      str = str[m.end():] 
      num_str = m.group().lstrip()
      #^ So the line number has no effect at all.
      #^ The parser will assign line numbers automatically.
      #^ It is used only for the user's convenience.
    else:
      num_str = ''
    is_proves_str = str.find(proves_str) == 0
    is_blank = (str == '' or str.isspace())
    is_fmla = not (str.startswith('#') or is_blank or is_proves_str)
    if not is_proves_str: # usual case
      if level > level0:
        if belongs_to_hyp:
          raise ValueError("get_str_li(): level increased " 
            f"while belongs_to_hyp\n\t{num_str}{str}")
        str_li_ret.append("{{")
        if is_fmla and not pat_hyp.search(str):
          if pat_hyp_false.search(str):
            raise ValueError("get_str_li(): watch for the typo " 
              f"'. hyp' instead of '.hyp'\n\t{num_str}{str}")
          else:        
            raise ValueError("get_str_li(): level increased but not is_hyp"
                            f"\n\t{num_str}{str}")
        belongs_to_hyp = True
        right_after_proves = False
      elif level < level0:
        if belongs_to_hyp or pat_hyp.search(str):
          raise ValueError("get_str_li(): level decreased " 
            f"while belongs_to_hyp\n\tor annotated with .hyp\n\t{num_str}{str}")
        while level < level0:
          str_li_ret.append("}}")
          level0 -= 1
        right_after_proves = False
      else: # level == level0 case
        if right_after_proves:
          if is_fmla and pat_hyp.search(str): # and level == level0
            raise ValueError("get_str_li(): same level and " 
              f"right_after_proves, but is_hyp\n"
              "\tPerhaps you should indent the following line:\n"
              f"\t{num_str}{str}")
          right_after_proves = False          
        if belongs_to_hyp:
          if is_fmla and not pat_hyp.search(str):
            raise ValueError("get_str_li(): belongs_to_hyp but not is_hyp\n"
              "\tPerhaps '.hyp' is misspelled, or \n"
              "\tyou forgot to insert the 'proves' line before the following:\n"
              f"\t{num_str}{str}") 
        else: 
          # If the previous line is a conclusion and the current line
          # is a hypothesis, then add ["}}", "{{"].
          if is_fmla and pat_hyp.search(str): # adjacent subproofs
            str_li_ret += ["}}","{{"]
            belongs_to_hyp = True
      if not is_fmla:
        # attach info about before/after proves_str
        suffix = '.hypo_' if belongs_to_hyp else '.conc_'
      else:
        suffix = ''
      # for all 3 cases (comment, blank and fmla)
      str_li_ret.append(str + suffix)
      level0 = level
    else: # proves_str in the current line
      if not belongs_to_hyp:
        raise ValueError("get_str_li(): proves_str in conclusion part\n"
        "\tPerhaps you should find and delete the 'proves' line\n" 
        "\twhich follows a non-hyp line.")
      belongs_to_hyp = False
      right_after_proves = True
  if verbose:
    print_lines(str_li_ret)
  return str_li_ret

def print_lines(lines: List[str]) -> None:
  """ This is a test driver function for get_str_li().
      Print lines with indentation. """
  level = 1
  for str in lines:
    if str.endswith('.hypo_') or str.endswith('.conc_'):
      str = str[:-6]
    if str == "}}":
      print(f"{('  ' * (level - 2))}{str}")
      level -= 1
    else:
      print(f"{('  ' * (level - 1))}{str}")
    if str == "{{":
      level += 1

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
    
def bLeafNode(s: str) -> bool:
  """test if s is a node id for a leaf node"""
  return Token.is_nat(s) # type: ignore

def bSubproof(s: str) -> bool:
  """test if s is a node id for a subproof"""
  return is_node_id(s) and '-' in s

#endregion util functions
