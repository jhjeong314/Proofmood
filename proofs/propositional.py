#region 0 
from typing import List, Tuple, Any
import re
import sys
sys.path.append('/Users/jooheejeong/Documents/Work/Proofmood/logical_formulas')
from first_order_logic_parse import *
from truth_table import * 

# line number = 1, 2, 3, ..
CONN_LIST = ['bot', 'neg', 'and', 'or', 'imp', 'iff']
INTRO_ELIM = ['intro', 'elim']
RULES_AUX = ['repeat', 'LEM', 'hyp']
VERT = '│'
PROVES = '├─'
TAB = '\t'

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

#endregion 0

class Ann: 
  """Annotation of a line of a proof tree"""
  def __init__(self, input_str: str):
    """input_str is a white-space stripped string."""
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

  def __str__(self) -> str:
    return self.build_fitch_text()[0]
  
  def build_fitch_text(self, l_num: int = 1, level: int = 1) \
                      -> Tuple[str, int]:
    """ Recursively build a Fitch-style proof text which looks like:
    │1. A imp B  .hyp
    │2. B imp C  .hyp
    ├─
    ││3. A   .hyp
    │├─
    ││4. B   .imp elim 1,3
    ││5. C   .imp elim 2,4
    │6. A imp C  .imp intro 3-5    
    """
    ret_str = f"{self.label}"
    if self.children:
      ret_l_num = len(self.children) # l_num increases by ret_l_num
      b_hyp = True 
      #^ 1st child of a subproof is always a hypothesis
      for kid in self.children:
        # We insert a separator line ├─ 
        # when the node type changes from hyp to conc.
        if b_hyp and not kid.label.is_hyp:
          ret_str += VERT * (level - 1) + PROVES + "\n"
          b_hyp = False
        
        v_str, l_num_inc = kid.build_fitch_text(l_num, level + 1)
        #^ level is the depth of the node in the tree, which is used to
        #^ determine the number of vertical bars to be inserted.
        if kid.label.type != 'subproof':
          ret_str += VERT * level + f"{l_num}. " + v_str + "\n"
        else:
          ret_str +=  v_str

        l_num += l_num_inc
    else:
      ret_l_num = 1
    return (ret_str, ret_l_num)
  
  def build_fitch_latex(self) -> str:
    """ Build a Fitch-style proof latex source. """
    raise NotImplementedError("build_fitch_latex() not implemented")
  
  # end of class Proof

class ProofParser:
  def __init__(self, lines: List[str], tabsize: int):
    self.lines = lines
    self.current_line = None
    self.tabsize = tabsize
    self.index = -1
    self.advance()

  def advance(self): # increment self.index and set self.current_line
    self.index += 1
    if self.index < len(self.lines):
      self.current_line = self.lines[self.index]
    else:
      self.current_line = None

  #region grammar  
  # <proof> ::= <hypothesis> "proves\n" <conclusion>
  # <hypothesis> ::= { <line> ".hyp"}+
  # <line> ::= <line_num> "." (<formula> "\n" | <comment> | <blank>)
  # <blank> ::= "\n"
  # <comment> ::= { <white_space> } "#" <utf8string> "\n"
  # <utf8string> ::= { [.] } # no "\n" allowed
  # <conclusion> ::= { (<line_annotated> | <subproof>) }+
  # <subproof> ::= "{{" <hypothesis0> "proves\n" <conclusion> "}}"
  #^ In our implementation, subproofs are not enclosed in curly braces.
  #^ Instead, they are indented like Python code.
  # <indent> ::= "\t" # tab
  # <hypothesis0> ::= <line>
  # <line_annotated> ::= <line_num> "." (<formula> <ann> "\n" | <comment> | <blank>)
  # <ann> ::= <rule_of_inference> <premise>
  # <premise> ::= { <node_identifier> "," }
  # <node_identifier> ::= <numeral> | <numeral> "-" <numeral>
  # <rule_of_inference> ::= "." <conn> ("intro" | "elim") | "repeat" | "LEM"
  # <conn> ::= "bot" | "not" | "and" | "or" | "imp" | "iff"
  # <numeral> ::= [1-9] { [0-9] }
  #endregion grammar
       
  def proof(self) -> ProofNode:
    raise NotImplementedError("proof() not implemented")
  
  # end of class ProofParser

def get_str_li(proof_str: str, tabsize: int) -> List[str]:
  """
  Convert proof_str to a list of strings, where the subproofs are
  indicated by double brace pairs.

  Indentation is the key to parsing a Fitch-style proof.
  In proof_str, indentations are indicated by tabs or spaces or VERTs.
  1. For each line, get the level from the number of leading spaces 
    or TABs or VERTs 
  2. Remove the leading line number if any from each line.
  3. From the change of level between lines, convert indentation to 
    double brace pairs to indicate subproofs.
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
  pat = re.compile(r'\d+\.\s*') # for matching line numbers
  level0 = 1
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
    if (m := pat.search(str)):
      str = str[m.end():]
    if str.find(proves_str) == -1:
      if level > level0:
        str_li_ret.append("{{")
      elif level < level0:
        while level < level0:
          str_li_ret.append("}}")
          level0 -= 1
      str_li_ret.append(str)
      level0 = level

  return str_li_ret

def print_lines(lines: List[str]) -> None:
  level = 1
  for str in lines:
    if str == "}}":
      print(f"{('  ' * (level - 2))}{str}")
      level -= 1
    else:
      print(f"{('  ' * (level - 1))}{str}")
    if str == "{{":
      level += 1

def parse_fitch(proof_str: str, tabsize: int = 2) -> ProofNode:  
  lines = get_str_li(proof_str, tabsize) 
  #^ list of strings, where the subproofs are indicated by double brace pairs
  #^ each element of the list corresponds to a line of the proof
  parser = ProofParser(lines, tabsize)

  return parser.proof() 
