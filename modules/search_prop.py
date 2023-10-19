from modules.validate_prop import *

def mykey(x: str):
  """ This is a key function for sorting the list of line numbers. """
  return int(x.split("-")[0])

class ProofNodeS(ProofNode):
  ''' S stands for Search. This class supplies numerous methods for 
      proof searching and editing.
  '''
  def __init__(self, p_node: ProofNode):
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
    
    for key in reversed(self.index_dict):
      tree_index = self.index_dict[key] 
      #^ key is line_num. e.g., '6', '8-12'
      p_node = self.get_p_node(tree_index) 
      if p_node.label.type == 'formula' and not p_node.label.is_hyp \
            and not self.verified(key):
        #^ self.verified(key) is used instead of more speedy 
        # p_node.validated. This is sort of a double check.
        fmla_node = p_node.label.formula.ast
        if (conn := fmla_node.token.value) in CONN_LIST:
          return ((key, tree_index), Connective(conn))
        else:
          return ((key, tree_index), "prime formula")
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

  def try_rule(self, rule: RuleInfer, ret_val, verbosity) -> bool:
    ''' ret_val is the return value of self.fmla_to_validate()
        conc_index is the tree_index of the conclusion formula
        p_conn is the principal connective of the conclusion formula
    '''
    match rule:
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
        raise ValueError(f"Rule {rule} is not supported.")

  #region Annotation search methods
  def prepare_search_ann(self, ret_val):
    ''' ret_val is the return value of self.fmla_to_validate() 
        Extract various information from ret_val and return them. 
        These information are used in searching annotations. 
    '''
    ((conc_ln, conc_index), p_conn) = ret_val
    conc_node_p = self.get_p_node(conc_index) # _p for ProofNode type
    conc_node = conc_node_p.label.formula.ast # Node type
    conc_fmla = FormulaProp(conc_node) # FormulaProp type
    return (conc_ln, conc_index, p_conn, 
            conc_node_p, conc_node, conc_fmla)

  def annotate_EX(self, conc_index, conc_ln, conc_node_p, 
                  ann_str, rule, verbosity) -> bool:
    ''' EX stands for EXtended. 
      When an annotation is found for the conclusion formula, 
      this method is called to annotate the conclusion and set
      the validated flag to True and print some messages depending
      on the verbosity level. 
      Returns True/False iff the annotation is found/not found.
    '''
    if ann_str:
      self.annotate(conc_index, Ann(ann_str))
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
    (conc_ln, conc_index, _, conc_node_p, _, conc_fmla) = \
      self.prepare_search_ann(ret_val)

    ann_str = '' # tentative value
    rule = RuleInfer.LEM.value
    # check principal connective
    if not conc_fmla.is_fmla_type(Connective.OR):
      return False
    # LEM doesn't need any premise.
    if conc_fmla.verified_by(RuleInfer.LEM):
      ann_str = f"{rule}"

    return self.annotate_EX(conc_index, conc_ln, conc_node_p, 
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
        if p_node.label.type == 'formula':
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
      if p_node1.label.type != 'formula':
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
        if p_node2.label.type != 'formula':
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
      if p_node1.label.type != 'formula':
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
        if p_node2.label.type != 'formula':
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
        if p_node.label.type == 'formula':
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
      if not p_node1.label.type in {'formula', 'subproof'}:
        continue
      # To expedite the search process, if the premise is a formula but
      # not an implication formula, then we skip it.
      if p_node1.label.type == 'formula' and not \
          FormulaProp(p_node1.label.formula.ast).\
            is_fmla_type(Connective.IMP):
        continue
      for line_num2, t_idx2 in reversed(self.index_dict.items()):
        if not self.is_earlier(t_idx2, conc_idx) or t_idx2 == t_idx1:
          continue
        p_node2 = self.get_p_node(t_idx2)
        if p_node2.label.type not in {'formula', 'subproof'}:
          continue
        if p_node1.label.type == 'subproof':
          node1 = self.subproof2implication(line_num1)
        else:
          node1 = p_node1.label.formula.ast
        if p_node2.label.type == 'subproof':
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
        if p_node.label.type == 'formula':
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
        if p_node.label.type == 'formula':
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
      if p_node1.label.type != 'formula' or \
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
        if p_node2.label.type not in {'formula', 'subproof'}:
          continue
        if p_node2.label.type == 'subproof':
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
          if p_node3.label.type not in {'formula', 'subproof'}:
            continue
          if p_node3.label.type == 'subproof':
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
      if p_node1.label.type != 'formula' or \
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
        if p_node2.label.type != 'formula':
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
      if p_node1.label.type != 'formula' or \
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
        if p_node2.label.type != 'formula':
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
  def clear_formula(self, pos: tree_index) -> None:
    """ Clear the formula at pos, which is a formula node. """
    self.update_formula(pos, Formula())

  def update_formula(self, pos: tree_index, new_fmla: Formula) -> None:
    """ Update the formula at pos, which is a formula node. """
    pass

  def clear_ann(self, pos: tree_index) -> None: 
    """ Clear the annotation at pos, which is a formula node. """
    self.annotate(pos, Ann())
    
  def annotate(self, pos: tree_index, ann: Ann) -> None: 
    """ Annotate the formula at pos with ann.
        pos must be the t_index of a formula node. """
    p_node = self.get_p_node(pos)
    p_node.label.ann = ann

  def insert_node(self, pos: tree_index, p_node: ProofNode, is_hyp=False) \
                  -> None:
    """ Insert p_node in the proof tree so that it's t_index becomes pos.
      Nodes at and after pos are shifted to the right.
      line_num, t_index as well as premises in annotations of the shifted
      nodes are updated accordingly. 

      is_hyp := True is rarely used. When multiple hypotheses are used
      in the level 0 proof, and we want to append a new hypothesis at 
      the end, then we need to set is_hyp to True.
    """
    pass

  def delete_node(self, pos: tree_index) -> None:
    """ Delete the p_node in the proof tree at pos.
      Nodes after pos are shifted to the left.
      line_num, t_index as well as premises in annotations of the shifted
      nodes are updated accordingly. 
    """
    pass

  # Using the editing methods above, we define the following.

  # 1. Add a blank line below the current line. If the current line is
  #     at the end of a subproof, then this newly added blank line becomes
  #     the last line of the current subproof.
  #    If the current line is a hyp, then for the level 0 proof, the newly
  #     added blank line is also a hyp. For subproofs this operation is
  #     not allowed.
  # 2. Insert a blank line above the current line at the same level.
  #    Details of the operation depends on the nature of the current line.
  # 3. Delete the current line.
  #    If the current line is the only line in hypothesis or in the 
  #     conclusion, then just clear the formula instead of deleting
  #     the line.
  # 4. Insert a blank line as the first conclusion, which means
  #     the conclusion right below the 'proves' separator.
  #    This operation is may be necessary when the there is a subproof
  #     at the position of the first conclusion.
  # 5. Add a blank subproof below the current line.
  #    Blank subproof consists of a single blank hypothesis and a single
  #     blank conclusion.
  # 6. Insert a blank subproof above the current line.
  # 7. End the current subproof, which means add a blank line below the
  #     end of the current subproof. The blank line's level is the same 
  #     as the current subproof's level.
  # 8. Delete the current subproof.

  #endregion Edit methods
