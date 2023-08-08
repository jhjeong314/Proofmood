from first_order_logic_parse import *

#region (1/2) Utils for rendering AST ## ------------------------------

def draw_ast(ast: Node, verbose=False):
  import matplotlib.pyplot as plt

  plt.rcParams["mathtext.fontset"] = "cm" 
    # cm = computer modern by Donald Knuth
  plt.rcParams["figure.dpi"] = 300 # default 100
  try:
    plt.rcParams["text.usetex"] = True 
    # without this, some LaTeX commands do not work
  except:
    # for Google Colab, which has somewhat limited capabilities when it comes to handling LaTeX.
    pass
  fig, ax = plt.subplots(1, 1, figsize=(3, 1.5))
  ax.set(aspect='equal')
  ax.set_xlim(0, 3) 
  ax.set_ylim(0, 1.5) 
  ax.axis('off')
  center_x = ax.get_xlim()[1] / 2
  center_y = ax.get_ylim()[1] / 2
  r = fig.canvas.get_renderer() # type: ignore

  tree = build_GNode(ast, center_x, center_y, ax, r)

  if verbose:
    print(tree)

  tree.draw_tree_GNode(plt)

def build_GNode(ast: Node, xpos, ypos, ax, r):
  # Node has 3 attributes: token: Token, children: list of Nodes, 
  #                        and type ::= "formula" | "term".

  # post-order traversal
  if(ast.children and ast.type=='formula'): # Node children
    if ast.token.token_type == 'quantifier':
      kid1 = ast.children[0] # a variable for the determiner
      kidd11 = kid1.children[0] # a formula for the determiner's scope
      children = [build_GNode(kidd11, xpos, ypos, ax, r)] # GNode children
    else:
      children = [build_GNode(kid, xpos, ypos, ax, r) 
                for kid in ast.children] # GNode children
  else:
    children = []  # GNode children

  if ast.type == 'formula':
    if ast.token.token_type in ('pred_pre', 'prop_letter'):
      label = Node.ident2latex(ast.token, 'latex')
    elif ast.token.token_type == 'quantifier':
      kid1 = ast.children[0] # a variable for the determiner
      kid1_label = Node.ident2latex(kid1.token)
      label = Node.token2latex(ast.token) + ' ' + kid1_label
    else:
      label = Node.token2latex(ast.token)
  else:
    label = Node.build_infix_term(ast, 'latex')
  
  txt = ax.text(xpos, ypos, '$' + label + '$', 
                ha='center', va='center', fontsize=6, alpha=0)
  return GNode(txt, ax, r, children=children)

#endregion

#region (2/2) Draw bussproof style Trees ## ---------------------------

class Tbox: # text object together with its position and size
  def __init__(self, txt, ax, r):
    # txt is a text object
    # r is a renderer
    self.txt = txt # matplotlib.text.Text object
      # txt.get_text() is the label (latex source string)
    bbox = txt.get_window_extent(renderer=r) # unit: pixel
    bbox_d = bbox.transformed(ax.transData.inverted()) 
      # unit: data coordinate. _d signifies data coordinate
    x, y = txt.get_position()
    self.x = x
    self.y = y
    self.width = bbox_d.width
    self.height = bbox_d.height

  def __str__(self):
    return (f"x = {self.x:.3f}, y = {self.y:.3f}, " + 
            f"w = {self.width:.3f}, h = {self.height:.3f}")
    
class GNode: # graph node
  def __init__(self, txt, ax, r, unit_len = 0.09, kx=2.2, ky=1, 
               overhang=0.07, children=None):
    # txt = ax.text(pos_x, pos_y, string, ..) is a text object
    # r is a renderer
    # dx is the horizontal distances between the children
    # dy is the vertical distance between the root and the children    
    # children is a list of GNode objects    
    # Root's position is (0, 0). When rendering, we will shift the
    # node's center to the center of the figure.
    # The root and each child's position is relative to the center
    # of the node.
    
    self.parent = None # This changes later iff 
                       # self is not the real(one and only) root.
    self.x = self.y = 0
    self.root = Tbox(txt, ax, r)
    self.children = None
    self.unit_height = unit_len
    self.overhang = overhang
    # Both (self.x, self.y) and (self.root.x, self.root.y) are 
    # positions of the root of self.  
    # The meaning of (self.x, self.y) depends on self.parent.
    # If self.parent is None, then (self.x, self.y) is not used at all.
    # If self.parent is not None, then (self.x, self.y) is the position 
    # of the root of self relative to the root of self.parent.
    # (self.root.x, self.root.y) has meaning iff self.parent is None.
    # It is the position (x, y) given when the text object was created
    # by ax.text(x, y, ...) 
    # Normally (actually, always) it is (center_x, center_y) of the axis.
    # The width of a GNode is a tricky concept.
    # Each GNode has 2 widths: self.width and self.root.width.
    # self.root.width is the width of the text object and automatically 
    # computed by matplotlib. self.width is the width of the GNode tree 
    # and computed by the code below.

    dx = kx * unit_len
    dy = ky * unit_len
    unit_height = self.unit_height 
      # height of each node (considered as a rectangle)
    if children:
      self.children = children
      n_kid = len(children)

      # Compute the total width of the node.
      kids_tot_width = sum([kid.width for kid in children]) + (n_kid-1)*dx
      self.width = max(kids_tot_width, self.root.width)

      # Compute the total height of the node
      max_height = max([kid.height for kid in children])
      tot_height = max_height + dy + unit_height
      self.height = tot_height

      # Get the position of each kid's root relative to the root of self.
      # xpos is relatively hard to obtain. ypos is easy.
  
      # Compute the kids_width, which is used to compute 
      #   each kid's root's xpos.
      if n_kid == 1:
        kids_width = children[0].root.width
      else:
        kids_width0 = (children[0].root.width/2 + children[0].width/2 + dx + 
                       children[-1].width/2 + children[-1].root.width/2)
        if n_kid == 2:
          kids_width = kids_width0
        else: # n_kid >= 3 case
          kids_width = (kids_width0 + (n_kid-2)*dx + 
                        sum([kid.width for kid in children[1:-1]]))
          
      w_root_l = children[0].root.width 
      w_root_r = children[-1].root.width
      for i, kid in enumerate(children):
        kid.parent = self
        kid.y = dy + unit_height
        if i==0:
          kid.x = -kids_width/2 + w_root_l/2
        else:
          kid.x = children[i-1].x + children[i-1].width/2 + dx + \
                  children[i].width/2
      
      assert abs(children[-1].x - kids_width/2 + w_root_r/2) < 1e-6, \
             "the last child's x is wrong"
    else:
      self.children = []
      self.width = self.root.width
      self.height = unit_height
    
  def __str__(self):
    return self.get_str()
  
  def get_str(self):
    # recursively print the tree
    s = (f"root: {self.root.txt.get_text()[1:-1]}, " +
         f"position: ({self.x:.3f}, {self.y:.3f}), " +
         f"width: {self.width:.3f}, height: {self.height:.3f}\n")
    if self.children:
      for kid in self.children:
        s += kid.get_str() # should revise using join()
    return s
   
  def draw_tree_GNode(self, plt1):
    # Draw the root.
    if self.parent is None:
      x_ref, y_ref = (self.root.x, self.root.y) 
        # normally, (x_ref, y_ref) = (center_x, center_y)
      if self.children: 
          # Then we shift the root down and maybe left/right too
          # so that the center of the whole tree coincides with 
          # the center of the axis.
        node_left = self.children[0]
        node_right = self.children[-1]
        x = x_ref
        y = y_ref - self.height/2 + self.unit_height/2
        self.root.txt.set_position((x, y))
        self.x, self.y = (x, y)
        # draw the horizontal line
        x11 = x + node_left.x - node_left.root.width/2 - self.overhang
        x12 = x - self.root.width/2 - self.overhang
        x1 = min(x11, x12)

        x21 = x + node_right.x + node_right.root.width/2 + self.overhang
        x22 = x + self.root.width/2 + self.overhang
        x2 = max(x21, x22)
        plt1.hlines(y + self.unit_height, x1, x2, linewidth=0.2, color='black')
      else: # Then there is no need to shift the root.
        pass
      self.root.txt.set_alpha(1)
    else:
      x_ref, y_ref = (self.parent.x, self.parent.y)
      x = x_ref + self.x
      y = y_ref + self.y
      self.root.txt.set_position((x, y))
      self.x, self.y = (x, y)
      self.root.txt.set_alpha(1)

    # Draw the children.
    if self.children:
      # draw horizontal line
      node_left = self.children[0]
      node_right = self.children[-1]
      x11 = self.x + node_left.x - node_left.root.width/2 - self.overhang
      x12 = self.x - self.root.width/2 - self.overhang
      x1 = min(x11, x12)

      x21 = self.x + node_right.x + node_right.root.width/2 + self.overhang
      x22 = self.x + self.root.width/2 + self.overhang
      x2 = max(x21, x22)

      plt1.hlines(self.y + self.unit_height, x1, x2,
                   linewidth=0.2, color='black')
      # draw subtrees
      for kid in self.children:
        kid.draw_tree_GNode(plt1)
# endregion
