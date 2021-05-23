from rtamt.ast.parser_visitor.stl.rtamtASTvisitor import STLrtamtASTvisitor
from rtamt.exception.stl.exception import STLNotImplementedException

from rtamt.operation.stl.discrete_time.offline.predicate_operation import PredicateOperation
from rtamt.operation.arithmetic.discrete_time.offline.addition_operation import AdditionOperation
from rtamt.operation.arithmetic.discrete_time.offline.multiplication_operation import MultiplicationOperation
from rtamt.operation.arithmetic.discrete_time.offline.subtraction_operation import SubtractionOperation
from rtamt.operation.arithmetic.discrete_time.offline.division_operation import DivisionOperation
from rtamt.operation.stl.discrete_time.offline.and_operation import AndOperation
from rtamt.operation.stl.discrete_time.offline.or_operation import OrOperation
from rtamt.operation.stl.discrete_time.offline.implies_operation import ImpliesOperation
from rtamt.operation.stl.discrete_time.offline.iff_operation import IffOperation
from rtamt.operation.stl.discrete_time.offline.xor_operation import XorOperation
from rtamt.operation.stl.discrete_time.offline.since_operation import SinceOperation
from rtamt.operation.arithmetic.discrete_time.offline.abs_operation import AbsOperation
from rtamt.operation.stl.discrete_time.offline.not_operation import NotOperation
from rtamt.operation.stl.discrete_time.offline.rise_operation import RiseOperation
from rtamt.operation.stl.discrete_time.offline.fall_operation import FallOperation
from rtamt.operation.stl.discrete_time.offline.once_operation import OnceOperation
from rtamt.operation.stl.discrete_time.offline.historically_operation import HistoricallyOperation
from rtamt.operation.stl.discrete_time.offline.always_operation import AlwaysOperation
from rtamt.operation.stl.discrete_time.offline.eventually_operation import EventuallyOperation
from rtamt.operation.stl.discrete_time.offline.previous_operation import PreviousOperation
from rtamt.operation.stl.discrete_time.offline.constant_operation import ConstantOperation
from rtamt.operation.stl.discrete_time.offline.once_bounded_operation import OnceBoundedOperation
from rtamt.operation.stl.discrete_time.offline.historically_bounded_operation import HistoricallyBoundedOperation
from rtamt.operation.stl.discrete_time.offline.since_bounded_operation import SinceBoundedOperation
from rtamt.operation.stl.discrete_time.offline.until_operation import UntilOperation
from rtamt.operation.stl.discrete_time.offline.until_bounded_operation import UntilBoundedOperation
from rtamt.operation.stl.discrete_time.offline.always_bounded_operation import AlwaysBoundedOperation
from rtamt.operation.stl.discrete_time.offline.eventually_bounded_operation import EventuallyBoundedOperation
from rtamt.operation.stl.discrete_time.offline.next_operation import NextOperation

class STLOfflineDiscreteTimePythonMonitor(STLrtamtASTvisitor):
    def __init__(self):
        self.node_monitor_dict = dict()

    def generate(self, node):
        self.visit(node, [])
        return self.node_monitor_dict

    def visitPredicate(self, node, pre_out, *args, **kwargs):
        monitor = PredicateOperation(node.operator)
        self.node_monitor_dict[node.name] = monitor

    def visitVariable(self, node, pre_out, *args, **kwargs):
        pass

    def visitAbs(self, node, pre_out, *args, **kwargs):
        monitor = AbsOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitAddition(self, node, pre_out, *args, **kwargs):
        monitor = AdditionOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitSubtraction(self, node, pre_out, *args, **kwargs):
        monitor = SubtractionOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitMultiplication(self, node, pre_out, *args, **kwargs):
        monitor = MultiplicationOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitDivision(self, node, pre_out, *args, **kwargs):
        monitor = DivisionOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitNot(self, node, pre_out, *args, **kwargs):
        monitor = NotOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitAnd(self, node, pre_out, *args, **kwargs):
        monitor = AndOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitOr(self, node, pre_out, *args, **kwargs):
        monitor = OrOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitImplies(self, node, pre_out, *args, **kwargs):
        monitor = ImpliesOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitIff(self, node, pre_out, *args, **kwargs):
        monitor = IffOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitXor(self, node, pre_out, *args, **kwargs):
        monitor = XorOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitEventually(self, node, pre_out, *args, **kwargs):
        monitor = EventuallyOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitAlways(self, node, pre_out, *args, **kwargs):
        monitor = AlwaysOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitUntil(self, node, pre_out, *args, **kwargs):
        monitor = UntilOperation()
        self.node_monitor_dict[node.name] = monitor


    def visitOnce(self, node, pre_out, *args, **kwargs):
        monitor = OnceOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitHistorically(self, node, pre_out, *args, **kwargs):
        monitor = HistoricallyOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitSince(self, node, pre_out, *args, **kwargs):
        monitor = SinceOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitRise(self, node, pre_out, *args, **kwargs):
        monitor = RiseOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitFall(self, node, pre_out, *args, **kwargs):
        monitor = FallOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitConstant(self, node, pre_out, *args, **kwargs):
        monitor = ConstantOperation(node.val)
        self.node_monitor_dict[node.name] = monitor

    def visitPrevious(self, node, pre_out, *args, **kwargs):
        monitor = PreviousOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitNext(self, node, pre_out, *args, **kwargs):
        monitor = NextOperation()
        self.node_monitor_dict[node.name] = monitor

    def visitTimedPrecedes(self, node, pre_out, *args, **kwargs):
        raise STLNotImplementedException('Precedes operator not implemented in STL offline monitor.')

    def visitTimedOnce(self, node, pre_out, *args, **kwargs):
        monitor = OnceBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitTimedHistorically(self, node, pre_out, *args, **kwargs):
        monitor = HistoricallyBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitTimedSince(self, node, pre_out, *args, **kwargs):
        monitor = SinceBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitTimedAlways(self, node, pre_out, *args, **kwargs):
        monitor = AlwaysBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitTimedEventually(self, node, pre_out, *args, **kwargs):
        monitor = EventuallyBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitTimedUntil(self, node, pre_out, *args, **kwargs):
        monitor = UntilBoundedOperation(node.begin, node.end)
        self.node_monitor_dict[node.name] = monitor

    def visitDefault(self, node, pre_out, *args, **kwargs):
        pass
