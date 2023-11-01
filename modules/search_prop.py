try:
  from modules.validate_prop import *
except ImportError:
  url = 'https://raw.githubusercontent.com/jhjeong314/Proofmood/main/modules'
  import httpimport
  with httpimport.remote_repo(url):
    from validate_prop import *  

def mykey(x: str):
  """ This is a key function for sorting the list of line numbers. """
  return int(x.split("-")[0])

class ProofNodeS(ProofNode): # type: ignore
  ''' S stands for Search. This class supplies numerous methods for 
      proof editing and searching.
  '''
  def __init__(self, p_node: ProofNode | None=None): # type: ignore
    if p_node is None: # type: ignore
      p_node = parse_fitch()
    assert isinstance(p_node, ProofNode),  \
      "ProofNodeS.__init__(): p_node must be a ProofNode instance."
    self.label = p_node.label
    self.children = p_node.children
    self.index = p_node.index
    self.line_num =p_node.line_num
    self.index_dict = p_node.index_dict
    self.validated = p_node.validated
  
  def fmla_to_validate(self) -> tuple:
    """ Return the ((line_num, tree_index), principal connective) 
          of the last formula that has not been validated yet, if
          the formula is not a prime formula.
        If the formula is a prime formula, then the second element
          of the return value is the string "prime formula".
        If all formulas have been validated, then return the 
          empty tuple().
        self must be the root of the whole proof. """
    assert isinstance(self.index_dict, dict), \
      "fmla_to_validate(): self.index_dict must be a dict."
    for key in reversed(self.index_dict):
      tree_idx = self.index_dict[key] 
      #^ key is line_num. e.g., '6', '8-12'
      p_node = self.get_p_node(tree_idx) 
      if p_node.label.type == LabelType.FORMULA and \
            not p_node.label.is_hyp and not self.verified(key):
        #^ self.verified(key) is used instead of more speedy 
        # p_node.validated. This is sort of a double check.
        fmla_node = p_node.label.formula.ast
        if (conn := fmla_node.token.value) in CONN_LIST:
          return ((key, tree_idx), Connective(conn))
        else:
          return ((key, tree_idx), "prime formula")
      else:
        continue

    return tuple() # all formulas have been validated
  
  def search_proof(self, verbosity: int=0) -> None:
    """ For each invalidated formula, starting from the last one, try to
        find and apply the appropriate inference rules to validate it.
        verbosity = 0: no output. just obtain a new proof
                  = 1: show messages
                  = 2: show messages and the proof trees    
    """
    while True:
      if (ret_val := self.fmla_to_validate()):
        for rule in RuleInfer:
          if self.try_rule(rule, ret_val, verbosity):
            # stop RuleInfer loop and go to the next invalidated formula
            break
          else:
            # try the next rule
            continue
        else:
          print("\nFailed to complete the proof search.\n")
          break # while loop
      else:
        # proof search successfully completed
        print("\nAll formulas have been validated.\n")
        break # while loop

  def try_rule(self, rule: RuleInfer, ret_val, verbosity) -> bool: # type: ignore
    ''' ret_val is the return value of self.fmla_to_validate()
        conc_idx is the tree_idx of the conclusion formula
        p_conn is the principal connective of the conclusion formula
    '''
    match rule: # type: ignore
      case RuleInfer.LEM:
        return self.try_LEM(ret_val, verbosity)
      case RuleInfer.REPEAT:
        return self.try_repeat(ret_val, verbosity)
      case RuleInfer.BOT_INTRO:
        return self.try_bot_intro(ret_val, verbosity)
      case RuleInfer.NOT_INTRO:
        return self.try_not_intro(ret_val, verbosity)
      case RuleInfer.AND_INTRO:
        return self.try_and_intro(ret_val, verbosity)
      case RuleInfer.OR_INTRO:
        return self.try_or_intro(ret_val, verbosity)
      case RuleInfer.IMP_INTRO:
        return self.try_imp_intro(ret_val, verbosity)
      case RuleInfer.IFF_INTRO:
        return self.try_iff_intro(ret_val, verbosity)
      case RuleInfer.BOT_ELIM:
        return self.try_bot_elim(ret_val, verbosity)
      case RuleInfer.NOT_ELIM:
        return self.try_not_elim(ret_val, verbosity)
      case RuleInfer.AND_ELIM:
        return self.try_and_elim(ret_val, verbosity)
      case RuleInfer.OR_ELIM:
        return self.try_or_elim(ret_val, verbosity)
      case RuleInfer.IMP_ELIM:
        return self.try_imp_elim(ret_val, verbosity)
      case RuleInfer.IFF_ELIM:
        return self.try_iff_elim(ret_val, verbosity)
      case RuleInfer.HYP:
        return False
      case _:
        raise ValueError(f"Rule {rule} is not supported.") # type: ignore

  #region Annotation search methods
  def prepare_search_ann(self, ret_val):
    ''' ret_val is the return value of self.fmla_to_validate() 
        Extract various information from ret_val and return them. 
        These information are used in searching annotations. 
    '''
    ((conc_ln, conc_idx), p_conn) = ret_val
    conc_node_p = self.get_p_node(conc_idx) # _p for ProofNode type
    conc_node = conc_node_p.label.formula.ast # Node type
    conc_fmla = FormulaProp(conc_node) # FormulaProp type
    return (conc_ln, conc_idx, p_conn, 
            conc_node_p, conc_node, conc_fmla)

  def annotate_EX(self, conc_idx, conc_ln, conc_node_p, 
                  ann_str, rule, verbosity) -> bool:
    ''' EX stands for EXtended. 
      When an annotation is found for the conclusion formula, 
      this method is called to annotate the conclusion and set
      the validated flag to True and print some messages depending
      on the verbosity level. 
      Returns True/False iff the annotation is found/not found.
    '''
    if ann_str:
      self.annotate(conc_idx, Ann(ann_str))
      conc_node_p.validated = True
      if verbosity > 0:
        print(f"'{rule}' rule successfully applied to line {conc_ln}.")
        # The following code is designed to identify potential bugs 
        # in one of the `try_some_rule()` methods. To invoke, just 
        # set verbosity = 2.
        # We have confidence in the correctness of `self.verified()`. 
        # The logic is clear and straightforward. However, it's worth 
        # noting that the `try_some_rule()` methods prioritize speed 
        # and may contain bugs.
        if verbosity > 1:
          if not self.verified(conc_ln):
            raise ValueError("annotate_EX(): Annotation "
                            f"'{ann_str}' for {conc_ln} is invalid.")
      ans = True
    else:
      if verbosity > 0:
        print(f"'{rule}' rule for line {conc_ln} failed.")
      ans = False
    if verbosity > 1:
      self.show_fitch_text()
      print()
    return ans

  def try_LEM(self, ret_val, verbosity: int) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, _, conc_fmla) = \
      self.prepare_search_ann(ret_val)

    ann_str = '' # tentative value
    rule = RuleInfer.LEM.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.OR):
      return False
    # LEM doesn't need any premise.
    if conc_fmla.verified_by(RuleInfer.LEM):
      ann_str = f"{rule}"

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p, 
                            ann_str, rule, verbosity)

  def try_repeat(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.REPEAT.value
    # look for a formula premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if self.is_earlier(t_idx, conc_idx):
        p_node = self.get_p_node(t_idx)
        if p_node.label.type == LabelType.FORMULA:
          node = p_node.label.formula.ast
          if conc_fmla.verified_by(RuleInfer.REPEAT,[node]):
            ann_str = f"{rule} {line_num}"
            break
    
    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)

  def try_bot_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.BOT_INTRO.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.BOT):
      return False
    # look for two formula premises
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      if p_node1.label.type != LabelType.FORMULA:
        continue
      # To expedite the search process, we selectively choose formulas 
      #   in the form of 'not alpha'.
      if p_node1.label.formula.ast.token.value != 'not':
        continue  
      node1 = p_node1.label.formula.ast.children[0]
      # then we look for another formula premise alpha
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type != LabelType.FORMULA:
          continue
        if p_node2.label.formula.ast == node1:
        # slower code commented out
        # if conc_fmla.verified_by(RuleInfer.BOT_INTRO,
        #     [p_node1.label.formula.ast, p_node2.label.formula.ast]):
          # make sure line_num1 > line_num2
          (line_num1, line_num2) = \
            sorted([line_num1, line_num2], reverse=True, key=mykey)
          ann_str = f"{rule} {line_num2},{line_num1}"
          break
      else: # if inner loop did not break, continue the outer loop
        continue
      break # if inner loop did break, break the outer loop too

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_not_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.NOT_INTRO.value
    if not conc_fmla.is_fmla_type(Connective.NOT):
      return False
    # look for a subproof premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if not bSubproof(line_num) or not self.is_earlier(t_idx, conc_idx):
        continue
      node = self.subproof2implication(line_num)
      if conc_fmla.verified_by(RuleInfer.NOT_INTRO,[node]):
        ann_str = f"{rule} {line_num}"
        break 

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_and_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.AND_INTRO.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.AND):
      return False
    # look for two formula premises
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      if p_node1.label.type != LabelType.FORMULA:
        continue
      # To expedite the search process, we selectively choose formulas 
      #   which is a subformula of the conclusion formula.
      prem1fmla = FormulaProp(p_node1.label.formula.ast)
      if not prem1fmla.verified_by(RuleInfer.AND_ELIM, [conc_node]):
        continue
      # then we look for another formula premise
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, t_idx1):
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type != LabelType.FORMULA:
          continue
        if conc_fmla.verified_by(RuleInfer.AND_INTRO,
            [p_node1.label.formula.ast, p_node2.label.formula.ast]):
          # make sure line_num1 > line_num2
          (line_num1, line_num2) = \
            sorted([line_num1, line_num2], reverse=True, key=mykey)
          ann_str = f"{rule} {line_num2},{line_num1}"
          break
      else: # if inner loop did not break, continue the outer loop
        continue
      break # if inner loop did break, break the outer loop too

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_or_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.OR_INTRO.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.OR):
      return False
    # look for a formula premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if self.is_earlier(t_idx, conc_idx):
        p_node = self.get_p_node(t_idx)
        if p_node.label.type == LabelType.FORMULA:
          node = p_node.label.formula.ast
          if conc_fmla.verified_by(RuleInfer.OR_INTRO,[node]):
            ann_str = f"{rule} {line_num}"
            break
    
    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_imp_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.IMP_INTRO.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.IMP):
      return False
    # look for a subproof premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if not bSubproof(line_num) or not self.is_earlier(t_idx, conc_idx):
        continue
      node = self.subproof2implication(line_num)
      if conc_fmla.verified_by(RuleInfer.IMP_INTRO,[node]):
        ann_str = f"{rule} {line_num}"
        break 

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)

  def try_iff_intro(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.IFF_INTRO.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.IFF):
      return False
    # Look for two premises either of which is a subproof or a formula.
    # They must not be comments or blank lines.
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      if not p_node1.label.type in {LabelType.FORMULA, LabelType.SUBPROOF}:
        continue
      # To expedite the search process, if the premise is a formula but
      # not an implication formula, then we skip it.
      if p_node1.label.type == LabelType.FORMULA and not \
          FormulaProp(p_node1.label.formula.ast).\
            is_fmla_type(Connective.IMP):
        continue
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type not in {LabelType.FORMULA, LabelType.SUBPROOF}:
          continue
        if p_node1.label.type == LabelType.SUBPROOF:
          node1 = self.subproof2implication(line_num1)
        else:
          node1 = p_node1.label.formula.ast
        if p_node2.label.type == LabelType.SUBPROOF:
          node2 = self.subproof2implication(line_num2)
        else:
          node2 = p_node2.label.formula.ast
        if conc_fmla.verified_by(RuleInfer.IFF_INTRO, [node1, node2]):
          # make sure line_num1 > line_num2
          (line_num1, line_num2) = \
            sorted([line_num1, line_num2], reverse=True, key=mykey)
          ann_str = f"{rule} {line_num2},{line_num1}"
          break
      else: # if inner loop did not break, continue the outer loop
        continue
      break # if inner loop did break, break the outer loop too

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)

  def try_bot_elim(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = ''
    rule = RuleInfer.BOT_ELIM.value
    # look for bot premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if self.is_earlier(t_idx, conc_idx):
        p_node = self.get_p_node(t_idx)
        if p_node.label.type == LabelType.FORMULA:
          prem_fmla_p = FormulaProp(p_node.label.formula.ast)
          if prem_fmla_p.is_fmla_type(Connective.BOT):
            ann_str = f"{rule} {line_num}"
            break
    
    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_not_elim(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, p_conn, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = ''
    rule = RuleInfer.NOT_ELIM.value
    # look for a subproof premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if not bSubproof(line_num) or not self.is_earlier(t_idx, conc_idx):
        continue
      node = self.subproof2implication(line_num)
      if conc_fmla.verified_by(RuleInfer.NOT_ELIM,[node]):
        ann_str = f"{rule} {line_num}"
        break 

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_and_elim(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = ''
    rule = RuleInfer.AND_ELIM.value
    # look for a premise
    for line_num, t_idx in reversed(self.index_dict.items()):
      if self.is_earlier(t_idx, conc_idx):
        p_node = self.get_p_node(t_idx)
        if p_node.label.type == LabelType.FORMULA:
          node = p_node.label.formula.ast
          if conc_fmla.verified_by(RuleInfer.AND_ELIM,[node]):
            ann_str = f"{rule} {line_num}"
            break
    
    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_or_elim(self, ret_val, verbosity) -> bool:
    # most complicated rule for propositional logic
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.OR_ELIM.value
    # look for 3 premises. 1st premise is a disjunction formula.
    # 2nd and 3rd premises are subproofs or implication formulas.
    search_success = False # jump out of all loops if True
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      # first, we look for a disjunction formula
      if p_node1.label.type != LabelType.FORMULA or \
            not p_node1.label.formula.is_fmla_type(Connective.OR):
        continue
      node1 = p_node1.label.formula.ast
      node1_or_lhs = node1.children[0]
      node1_or_rhs = node1.children[1]
      # Next, we search for two premises, each of which can be either 
      #   a subproof or an implication formula.
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type not in {LabelType.FORMULA, LabelType.SUBPROOF}:
          continue
        if p_node2.label.type == LabelType.SUBPROOF:
          node2 = self.subproof2implication(line_num2)
        else:
          node2 = p_node2.label.formula.ast
          if not Formula(node2).is_fmla_type(Connective.IMP):
            continue
        node2_imp_lhs = node2.children[0]
        if node2_imp_lhs != node1_or_lhs and node2_imp_lhs != node1_or_rhs:
          continue
        node2_imp_rhs = node2.children[1]
        if node2_imp_rhs != conc_node:
          continue
        for line_num3, t_idx3 in reversed(self.index_dict.items()):
          if not self.is_earlier(t_idx3, t_idx2) or t_idx3 == t_idx1:
            continue
          p_node3 = self.get_p_node(t_idx3)
          if p_node3.label.type not in {LabelType.FORMULA, LabelType.SUBPROOF}:
            continue
          if p_node3.label.type == LabelType.SUBPROOF:
            node3 = self.subproof2implication(line_num3)
          else:
            node3 = p_node3.label.formula.ast
            if not Formula(node3).is_fmla_type(Connective.IMP):
              continue
          node3_imp_lhs = node3.children[0]
          if node3_imp_lhs == node2_imp_lhs:
            continue
          if node3_imp_lhs != node1_or_lhs and \
             node3_imp_lhs != node1_or_rhs:
            continue
          node3_imp_rhs = node3.children[1]
          if node3_imp_rhs == conc_node:
            search_success = True
            # make sure line_num1 > line_num2 > line_num3
            (line_num1, line_num2, line_num3) = \
              sorted([line_num1, line_num2, line_num3], reverse=True, key=mykey)
            ann_str = f"{rule} {line_num3},{line_num2},{line_num1}"
            break
        if search_success:
          break
      if search_success:
        break

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  def try_imp_elim(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.IMP_ELIM.value
    # look for two formula premises
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      # first, we look for an implication formula
      if p_node1.label.type != LabelType.FORMULA or \
         not p_node1.label.formula.is_fmla_type(Connective.IMP):
        continue
      node1 = p_node1.label.formula.ast
      node_antecedent = node1.children[0]
      node_consequent = node1.children[1]
      if node_consequent != conc_node:
        continue
      # then we look for another formula premise
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type != LabelType.FORMULA:
          continue
        if p_node2.label.formula.ast == node_antecedent:
          # make sure line_num1 > line_num2
          (line_num1, line_num2) = \
            sorted([line_num1, line_num2], reverse=True, key=mykey)
          ann_str = f"{rule} {line_num2},{line_num1}"
          break
      else: # if inner loop did not break, continue the outer loop
        continue
      break # if inner loop did break, break the outer loop too

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)

  def try_iff_elim(self, ret_val, verbosity) -> bool:
    (conc_ln, conc_idx, _, conc_node_p, conc_node, conc_fmla) = \
      self.prepare_search_ann(ret_val)
    ann_str = '' # tentative value
    rule = RuleInfer.IFF_ELIM.value
    # look for two formula premises
    for line_num1, t_idx1 in reversed(self.index_dict.items()):
      if not self.is_earlier(t_idx1, conc_idx):
        continue
      p_node1 = self.get_p_node(t_idx1)
      # first, we look for an iff formula
      if p_node1.label.type != LabelType.FORMULA or \
         not p_node1.label.formula.is_fmla_type(Connective.IFF):
        continue
      node1 = p_node1.label.formula.ast
      prem_node_lhs = node1.children[0]
      prem_node_rhs = node1.children[1]
      if prem_node_lhs != conc_node and prem_node_rhs != conc_node:
        continue
      prem_node_other = prem_node_rhs if prem_node_lhs == conc_node \
                        else prem_node_lhs
      # then we look for another formula premise
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type != LabelType.FORMULA:
          continue
        if p_node2.label.formula.ast == prem_node_other:
          # make sure line_num1 > line_num2
          (line_num1, line_num2) = \
            sorted([line_num1, line_num2], reverse=True, key=mykey)
          ann_str = f"{rule} {line_num2},{line_num1}"
          break
      else: # if inner loop did not break, continue the outer loop
        continue
      break # if inner loop did break, break the outer loop too

    return self.annotate_EX(conc_idx, conc_ln, conc_node_p,
                            ann_str, rule, verbosity)
  
  #endregion Annotation search methods

  #region Edit methods

  def insert_node(self, pos: int | str | List[int], 
          p_node: ProofNode | None=None, # type: ignore
          go_above: bool=True, level_down: bool=False) -> None:
    """ This method utilizes insert_nodes() method. """
    if isinstance(p_node, ProofNode): # type: ignore
      p_node_li = [p_node]
    else:
      p_node_li = [] # later, this will be a list of a single blank line
    self.insert_nodes(pos, p_node_li, go_above, level_down)

  def insert_nodes(self, pos: int | str | List[int], 
          p_node_li: List[ProofNode]=[], # type: ignore
          go_above: bool=True, level_down: bool=False) -> None:
    """ 
      This method is an extension of the insert_node() method.
      We can insert a list of nodes `p_node_li` at once with this method.
      If this argument is not supplied, then a blank line is inserted.

      `pos` may be a position of a line or a subproof.
      `p_node_li` is a chunk of nodes(line or subproof), which means
        a list of consecutive nodes sharing a common parent node.
    
      level_down is used only when go_above is False and pos refers to
        the youngest kid (and thus a conclusion) and pos is not in the 
        base level. If any of these three conditions is not met, then 
        the value of level_down is ignored.

      Inserting into the hypothesis section requires careful consideration. 
        It cannot accommodate a subproof and should not accept more than 
        one formula.
        
      As the result of the insertion, the lines below the insertion node
        are shifted, and we have to update line_num and index, which is
        easily done by the following:
          self.build_index()
          self.index_dict = self.build_index_dict()
      But updating the premises of the shifted lines needs some work,
        and we do it by calling self.adjust_premises() method. """
    # work on the destination node and its parent
    p_node_dest = self.get_p_node(pos)
    dest_idx = p_node_dest.index
    dest_ln = p_node_dest.line_num
    assert len(dest_idx) > 1, \
      f"insert_nodes(): You cannot insert a node at the root."
    dest_in_hyp = p_node_dest.label.is_hyp
    # p_node_li = [] case is handled below.
    # We let p_node_li = [p_node] where p_node is a blank line.
    if not p_node_li:
      label0 = NodeLabel(type=LabelType.BLANK_HYP) if dest_in_hyp \
              else NodeLabel(type=LabelType.BLANK_CONC)
      p_node_li = [ProofNode(label=label0)]

    assert all([isinstance(p_n, ProofNode) for p_n in p_node_li]), \
      f"insert_nodes(): isinstance(p_node, ProofNode) required."
    
    # determine the parent node and the rank of
    # the node to be inserted. (first kid's rank is 0)
    dest_idx_parent = dest_idx[:-1]
    rank_insert = dest_idx[-1]

    # If the destination is in hypothesis, then 
    # 1. no subproof can be inserted.
    # 2. for proper subproofs, 
    #    2.1 at most one formula can exist.
    #    2.2 when a formula or a blank line is inserted, it is inserted
    #        as a conclusion of the parent proof one level below.
    if dest_in_hyp:
      if p_node_li:
        if any([p_node.label.type == LabelType.SUBPROOF 
                for p_node in p_node_li]):
          raise Exception("insert_node(): Cannot insert a subproof into"
                      " a hypothesis.")
      if len(dest_idx) >= 3: # proper subproof case
        if go_above:
          if len(p_node_li) > 1:
            raise Exception("insert_nodes(): Cannot insert more than"
                            " one node into a hypothesis of a subproof.")
          p_node = p_node_li[0]
          if p_node.label.type in {LabelType.FORMULA, LabelType.BLANK_HYP}:
            # insert p_node in the conclusion part of the parent subproof
            dest_idx_parent = dest_idx[:-2]
            rank_insert = dest_idx[-2]
            dest_in_hyp = False
            if p_node.label.type == LabelType.BLANK_HYP:
              p_node.label.type = LabelType.BLANK_CONC
              p_node.label.is_hyp = False
              p_node_li = [p_node]
        else:
          # inserting any node below a hypothesis is not allowed.
          raise Exception("insert_nodes(): Cannot insert any node below"
                          " within a hypothesis of a subproof.")

    parent_node = self.get_p_node(dest_idx_parent)
    # go_above = False case
    if not go_above: # dest_in_hyp is False here
      if level_down and len(dest_idx) >= 3 and \
         len(parent_node.children) == rank_insert + 1:
        #^ If dest_idx is the youngest child, finish the current subproof 
        #^ and insert p_node one level down.
        rank_insert = dest_idx_parent[-1] + 1
        dest_idx_parent = dest_idx_parent[:-1] # = dest_idx[:-2]
        parent_node = self.get_p_node(dest_idx_parent)
      else: # insert below the destination node
        rank_insert += 1

    # the insertion is done here
    parent_node.children[rank_insert:rank_insert] = p_node_li

    self.build_index()
    self.index_dict = self.build_index_dict()
    n_lines = sum([num_nodes(p_n) for p_n in p_node_li]) 
    self.adjust_premises(dest_idx, dest_ln, n_lines, 
                         opt='insert', go_above=go_above)
    #^ Actually, it would have been a little bit easier if we adjusted 
    #^ premises before the insertion action.

    self.validate_all()

  def delete_node(self, pos: int | str | List[int], bReturn=False):
    ''' This method utilizes the delete_nodes() method. '''
    if isinstance(pos, list):
      p_node = self.get_p_node(pos)
      pos = p_node.line_num

    self.delete_nodes(pos, bReturn)
  
  def delete_nodes(self, chunk, bReturn=False):
    """ Delete the nodes in the chunk. 
      `chunk` is a string that looks like 'a~b', where 
      a, b are of the form 'n' or 's-e' 
        Chunk represents a sequence of consecutive siblings sharing 
      a common parent. 
        If a subproof has line_num a-b, then chunk:='a-b' deletes the
      entire subproof, and chunk:='a~b' clears all hyp and conc of the
      subproof and leaves a blank subproof.
        All subproofs must have at least one hypothesis and at least
      one conclusion. Therefore, when delete all the lines of the 
      hypothesis or the conclusion section of a subproof, we leave a 
      blank line there.
        As the result of the insertion, the lines below the insertion 
      node are shifted, and we have to update line_num and index, which 
      is easily done by the following:
          self.build_index()
          self.index_dict = self.build_index_dict()
      But updating the premises of the shifted lines needs some work,
        and we do it by calling self.adjust_premises() method. """
    # Work on the nodes to be deleted.
    p_node_del_li = self.get_p_node_li(chunk)
    del_idx_li = [p_node.index for p_node in p_node_del_li]
    del_ln_li = [p_node.line_num for p_node in p_node_del_li]
    parent_idx = del_idx_li[0][:-1]
    parent_node = self.get_p_node(parent_idx)
    # If there is only one hypothesis or one conclusion, then we cannot
    # delete it. Instead, we clear it.  To handle this, we prepare some 
    # variables here.
    n_hyp = parent_node.num_nodes_hyp()
    n_conc = parent_node.num_nodes_conc()
    n_hyp_del = sum([p_node.label.is_hyp for p_node in p_node_del_li])
    n_conc_del = len(p_node_del_li) - n_hyp_del

    rank_s = del_idx_li[0][-1]
    rank_e = del_idx_li[-1][-1] # = rank_s + len(p_node_del_li) - 1

    n_lines_sub = 0
    # delete hypotheses
    if n_hyp_del == n_hyp: # we must leave a blank hyp in this case
      self.clear_node(parent_idx + [0])
      del parent_node.children[1:n_hyp]
      n_hyp_del = n_hyp - 1
      n_lines_sub -= 1
    elif n_hyp_del > 0: # easier case
      del parent_node.children[rank_s:rank_s+n_hyp_del]
    # delete conclusions
    if n_conc_del == n_conc: # we must leave a blank conc in this case
      self.clear_node(parent_idx + [max(s_conc := n_hyp - n_hyp_del, 1)])
      del parent_node.children[s_conc+1:]
      n_lines_sub -= 1
    elif n_conc_del > 0: 
      # need some work here because hypotheses may have been deleted
      s_conc = rank_e - n_hyp_del - n_conc_del + 1
      e_conc = rank_e - n_hyp_del + 1
      del parent_node.children[s_conc:e_conc]

    self.build_index()
    self.index_dict = self.build_index_dict()
    n_lines = sum([num_nodes(p_n) for p_n in p_node_del_li]) + n_lines_sub
    n_del_nodes = len(p_node_del_li)

    self.adjust_premises(del_idx_li[0], del_ln_li[0], n_lines, 
                        opt='delete', n_del_nodes=n_del_nodes)
    self.validate_all()

    if bReturn:
      return p_node_del_li

  def adjust_premises(self, dest_idx, dest_ln: str, n_lines, 
                      opt, go_above=True, n_del_nodes=1) -> None:
    ''' When a node is inserted or deleted, we need to adjust the premises 
      in the annotations of the lines after dest_ln.
        opt is either 'insert' or 'delete'.
        dest_ln is a string which represents a position of a line or 
      a subproof. In the latter case, and in this case only, the value of
      the argument n_lines is >= 2. 
        This method is not recursively called. It calls the Ann class's
      adjust_premises() method.
    '''
    
    if '-' in dest_ln: 
      dest_ln = dest_ln.split('-')[0] # hyp line of the subproof
    for v_ln in self.index_dict: # type: ignore
      # self.index_dict is of the tree after the insertion/deletion
      p_node = self.get_p_node(v_ln)
      if p_node.label.type != LabelType.FORMULA or p_node.label.is_hyp:
        continue
      if not int(v_ln) >= int(dest_ln):
        #^ do not use is_earlier() here
        continue
      ann = p_node.label.ann
      if not isinstance(ann, Ann) or not ann.premise:
        continue
      if opt == 'delete': # easier case
        ann.adjust_premises(self, dest_ln, v_ln, n_lines, opt)
      elif opt == 'insert':
        if int(v_ln) >= (e := int(dest_ln) + n_lines):
           dest_idx1 = dest_idx[:-1] + [dest_idx[-1] + 1]
           if go_above or (int(v_ln) > e and 
                           not li_extends(p_node.index, dest_idx1)):
             ann.adjust_premises(self, dest_ln, v_ln, n_lines, opt)
      else:
        raise Exception("adjust_premises(): opt must be either"
                        " 'insert' or 'delete'.")

  def update_formula(self, pos, new_fmla: Formula) -> None: # type: ignore
    import copy
    """ The line can be a formula(hyp or conc), a comment or a blank line. 
        Non-formula line becomes a formula line, and the content
          is lost. 
        Formula line's formula is replaced with new_fmla.
        Its ann remains unchanged. """
    p_node = self.get_p_node(pos)
    p_node.label.type = LabelType.FORMULA
    p_node.label.formula = copy.deepcopy(new_fmla) # type: ignore
    p_node.label.line = f"{new_fmla}\t .{p_node.label.ann}" # type: ignore
    self.validate_all()

  def annotate(self, pos, ann: Ann) -> None: # type: ignore
    import copy
    """ Annotate the formula at pos with ann.
        pos must be the t_idx of a conclusion formula node. """
    p_node = self.get_p_node(pos)
    l_num = p_node.line_num
    assert p_node.label.type == LabelType.FORMULA, \
      f"annotate(): pos {pos} is not a formula node."
    assert not p_node.label.is_hyp, \
      f"annotate(): pos '{l_num}' is a hypothesis, which cannot be annotated."
    assert isinstance(ann, Ann), \
      f"annotate(): ann must be an Ann object."
    p_node.label.ann = copy.deepcopy(ann)
    p_node.validated = self.verified(l_num)

  def clear_ann(self, pos) -> None: 
    """ Clear the annotation at pos, which is a formula node. """
    self.annotate(pos, Ann())
    
  def clear_node(self, pos) -> None:
    """ Make the node at pos a blank formula. 
        The node may be either a formula or a subproof.
        Blank formula means 
          hyp case: top .hyp
          conc case: top <empty annotation> """
    p_node = self.get_p_node(pos)
    p_node.label.type = LabelType('formula')
    p_node.label.formula = Formula()
    if p_node.label.is_hyp:
      p_node.label.line = "top .hyp"
      p_node.label.ann = Ann('hyp')
    else:
      p_node.label.line = "top ."
      p_node.label.ann = Ann()

    self.validate_all()

  def replace_node(self, pos, p_node) -> None:
    assert isinstance(p_node, ProofNode), \
      f"insert_node(): p_node must be a ProofNode."
    p_node_dest = self.get_p_node(pos)
    if p_node_dest.label.is_hyp and \
       p_node.label.type == LabelType.SUBPROOF:
      raise Exception("replace_node(): Cannot replace a hypothesis" 
                      " with a subproof.")
    t_idx = p_node_dest.index
    parent_idx = t_idx[:-1]
    parent_node = self.get_p_node(parent_idx)
    rank_dest = t_idx[-1]
    parent_node.children[rank_dest] = p_node
    self.build_index()
    self.index_dict = self.build_index_dict()
    self.validate_all()

  # copy/cut/move/duplicate nodes

  def copy_node(self, pos) -> ProofNode: # type: ignore
    ''' This method utilizes the copy_nodes() method. '''
    return self.copy_nodes(pos)[0]
  
  def copy_nodes(self, chunk) -> List[ProofNode]: # type: ignore
    import copy

    return copy.deepcopy(self.get_p_node_li(chunk))
    
  def cut_node(self, pos) -> ProofNode: # type: ignore
    """ Cut the node in the chunk and return it. """
    return self.cut_nodes(pos)[0]
  
  def cut_nodes(self, chunk) -> List[ProofNode]: # type: ignore
    """ Cut the nodes in the chunk and return them as a list. """
    return self.delete_nodes(chunk, bReturn=True) # type: ignore   
  
  def move_node(self, pos_src, pos_dest, go_above=True) -> None:
    ''' This method utilizes the move_nodes() method. '''
    self.move_nodes(pos_src, pos_dest, go_above)

  def move_nodes(self, chunk, pos_dest, go_above=True) -> None:
    ''' This method is basically does the job of cut_nodes() followed by
      insert_nodes(). Some preparatory work is necessary. '''
    # source nodes
    p_node_li = self.get_p_node_li(chunk) 
    #^ Checking the integrity of `chunk` is done above.

    # destination node
    t_idx_dest = (p_node_dest := self.get_p_node(pos_dest)).index
    l_num_dest = p_node_dest.line_num

    # compatibility of src and dest positions
    for p_node in p_node_li:
      assert isinstance(p_node, ProofNode)
      t_idx_src = p_node.index
      assert not li_compatible(t_idx_src, t_idx_dest), \
        f"move_nodes(): source index '{t_idx_src}' and destination index" \
        f" '{t_idx_dest}'\n\tshould not be compatible."
      
    l_num_src = p_node_li[0].line_num # type: ignore
    if '-' in l_num_src:
      l_num_src = l_num_src.split('-')[0]
    if '-' in l_num_dest:
      l_num_dest = l_num_dest.split('-')[0]

    if int(l_num_src) < int(l_num_dest):
      # destination changes after the deletion of p_node_src
      n_lines = sum([num_nodes(p_n) for p_n in p_node_li]) 
      l_num_dest = str(int(l_num_dest) - n_lines)

    self.delete_nodes(chunk)
    # We use l_num_dest instead of pos_dest because pos_dest may 
    # have been changed by the deletion of `chunk`.
    self.insert_nodes(l_num_dest, p_node_li, go_above)
    
  def duplicate_node(self, pos_src, pos_dest, go_above=True) -> None:
    ''' This method utilizes the duplicate_nodes() method. '''
    self.duplicate_nodes(pos_src, pos_dest, go_above)

  def duplicate_nodes(self, chunk, pos_dest, go_above=True) -> None:
    """ This method is basically does the job of copy_nodes() followed 
      by insert_nodes(). Much simpler than move_nodes(). """
    p_node_li = self.copy_nodes(chunk)
    #^ Checking the integrity of `chunk` is done above.
    self.insert_nodes(pos_dest, p_node_li, go_above)   

  def get_p_node_li(self, chunk) -> List[ProofNode]: # type: ignore
    ''' Get p_node_li from `chunk`.
        Duplication is the responsibility of the caller. '''    

    assert isinstance(self.index_dict, dict), \
      f"get_p_node_li(): self.index_dict is not dict?"
    assert isinstance(chunk, str) or isinstance(chunk, int), \
      f"get_p_node_li(): chunk='{chunk}'?"
    # Various formats of chunk are allowed.
    chunk = str(chunk) # we allow something like chunk = 7
    s_li = chunk.split('~')
    if len(s_li) == 2:
      pos_s = s_li[0]
      idx_s = self.index_dict.get(pos_s)
      pos_e = s_li[1]
      idx_e = self.index_dict.get(pos_e)
      assert self.index_dict[pos_s][:-1] == self.index_dict[pos_e][:-1], \
        f"get_p_node_li(): two positions '{pos_s}' and '{pos_e}'" \
        "\n\tshould share a common parent."
      p_node_li = [self.get_p_node(pos) for pos in self.index_dict 
                    if idx_within(self.index_dict[pos], idx_s, idx_e)]
    elif len(s_li) == 1:
      p_node_li = [self.get_p_node(chunk)]
    else:
      raise Exception("get_p_node_li(): wrong chunk format.")
    
    return p_node_li
      
  #endregion Edit methods
