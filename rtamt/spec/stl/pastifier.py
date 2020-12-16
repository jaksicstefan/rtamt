from rtamt.spec.stl.visitor import STLVisitor

from rtamt.interval.interval import Interval
from rtamt.node.stl.predicate import Predicate
from rtamt.node.stl.variable import Variable
from rtamt.node.stl.neg import Neg
from rtamt.node.stl.conjunction import Conjunction
from rtamt.node.stl.disjunction import Disjunction
from rtamt.node.stl.implies import Implies
from rtamt.node.stl.iff import Iff
from rtamt.node.stl.xor import Xor
from rtamt.node.stl.eventually import Eventually
from rtamt.node.stl.always import Always
from rtamt.node.stl.once import Once
from rtamt.node.stl.historically import Historically
from rtamt.node.stl.timed_precedes import TimedPrecedes
from rtamt.node.stl.since import Since
from rtamt.node.stl.addition import Addition
from rtamt.node.stl.subtraction import Subtraction
from rtamt.node.stl.multiplication import Multiplication
from rtamt.node.stl.division import Division
from rtamt.node.stl.abs import Abs
from rtamt.node.stl.fall import Fall
from rtamt.node.stl.rise import Rise
from rtamt.node.stl.constant import Constant
from rtamt.node.stl.previous import Previous
from rtamt.node.stl.timed_always import TimedAlways
from rtamt.node.stl.timed_eventually import TimedEventually
from rtamt.node.stl.timed_historically import TimedHistorically
from rtamt.node.stl.timed_once import TimedOnce
from rtamt.node.stl.timed_since import TimedSince
from rtamt.node.stl.timed_until import TimedUntil

class STLPastifier(STLVisitor):

    def __init__(self, is_pure_python=True):
        self.is_pure_python = is_pure_python
        
    @property
    def is_pure_python(self):
        return self.__is_pure_python

    @is_pure_python.setter
    def is_pure_python(self, is_pure_python):
        self.__is_pure_python = is_pure_python

    def pastify(self, element):
        return self.visit(element, [element.horizon])

    def visitConstant(self, element, args):
        node = Constant(element.val, self.is_pure_python)
        return node

    def visitPredicate(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Predicate(child1_node, child2_node, element.operator, self.is_pure_python)
        return node

    def visitVariable(self, element, args):
        horizon = args[0]
        node = Variable(element.var, element.field, element.io_type)
        if horizon > 0:
            node = TimedOnce(node, horizon, horizon, self.is_pure_python)
        return node

    def visitAddition(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Addition(child1_node, child2_node, self.is_pure_python)
        return node

    def visitMultiplication(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Multiplication(child1_node, child2_node, self.is_pure_python)
        return node

    def visitSubtraction(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Subtraction(child1_node, child2_node, self.is_pure_python)
        return node

    def visitDivision(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Division(child1_node, child2_node, self.is_pure_python)
        return node

    def visitAbs(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Abs(child_node, self.is_pure_python)
        return node

    def visitRise(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Rise(child_node, self.is_pure_python)
        return node

    def visitFall(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Fall(child_node, self.is_pure_python)
        return node

    def visitNot(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Neg(child_node, self.is_pure_python)
        return node

    def visitAnd(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Conjunction(child1_node, child2_node, self.is_pure_python)
        return node

    def visitOr(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Disjunction(child1_node, child2_node, self.is_pure_python)
        return node

    def visitImplies(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Implies(child1_node, child2_node, self.is_pure_python)
        return node

    def visitIff(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Iff(child1_node, child2_node, self.is_pure_python)
        return node

    def visitXor(self, element, args):
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = Xor(child1_node, child2_node, self.is_pure_python)
        return node

    def visitEventually(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Eventually(child_node, self.is_pure_python)
        return node

    def visitTimedEventually(self, element, args):
        horizon = args[0] - element.end
        node = self.visit(element.children[0], [horizon])
        begin = 0
        end = element.end - element.begin
        if end > 0:
            node = TimedOnce(node, begin, end, self.is_pure_python)
        return node

    def visitAlways(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Always(child_node, self.is_pure_python)
        return node

    def visitTimedAlways(self, element, args):
        horizon = args[0] - element.end
        node = self.visit(element.children[0], [horizon])
        begin = 0
        end = element.end - element.begin
        if end > 0:
            node = TimedHistorically(node, begin, end, self.is_pure_python)
        return node

    def visitTimedUntil(self, element, args):
        horizon = args[0] - element.end
        begin = element.begin
        end = element.end
        child1_node = self.visit(element.children[0], [horizon])
        child2_node = self.visit(element.children[1], [horizon])
        node = TimedPrecedes(child1_node, child2_node, begin, end, self.is_pure_python)
        return node

    def visitUntil(self, element, args):
        return None

    def visitOnce(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Once(child_node, self.is_pure_python)
        return node

    def visitTimedOnce(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = TimedOnce(child_node, element.begin, element.end, self.is_pure_python)
        return node

    def visitPrevious(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Previous(child_node, self.is_pure_python)
        return node

    def visitNext(self, element, args):
        horizon = args[0] - 1
        child_node = self.visit(element.children[0], [horizon])


        return child_node

    def visitHistorically(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = Historically(child_node, self.is_pure_python)
        return node

    def visitTimedHistorically(self, element, args):
        child_node = self.visit(element.children[0], args)
        node = TimedHistorically(child_node, element.begin, element.end, self.is_pure_python)
        return node

    def visitSince(self, element, args):
        child_node_1 = self.visit(element.children[0], args)
        child_node_2 = self.visit(element.children[1], args)
        node = Since(child_node_1, child_node_2, self.is_pure_python)
        return node

    def visitTimedSince(self, element, args):
        child_node_1 = self.visit(element.children[0], args)
        child_node_2 = self.visit(element.children[1], args)
        node = TimedSince(child_node_1, child_node_2, element.begin, element.end, self.is_pure_python)
        return node

    def visitTimedPrecedes(self, element, args):
        end = element.end
        begin = element.begin
        child1_node = self.visit(element.children[0], args)
        child2_node = self.visit(element.children[1], args)
        node = TimedPrecedes(child1_node, child2_node, begin, end, self.is_pure_python)
        return node

    def visitDefault(self, element):
        return None