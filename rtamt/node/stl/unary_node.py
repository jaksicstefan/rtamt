from rtamt.node.stl.node import Node

class UnaryNode(Node):

    def __init__(self, child):
        """Constructor for Node"""
        super(Node, self).__init__()
        self.addChild(child)



