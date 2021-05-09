from rtamt.semantics.discrete_time_offline_semanitcs import DiscreteTimeOfflineSemanitcs
from rtamt.enumerations.comp_oper import StlComparisonOperator
from rtamt.exception.ltl.exception import LTLException #TODO: why ltl is here?

class PredicateSemantics(DiscreteTimeOfflineSemanitcs):
    def __init__(self, op):
        self.op = op

    def reset(self):
        pass

    def evaluate(self, left, right):

        out = []
        for i in range(len(left)):
            if self.op.value == StlComparisonOperator.EQ.value:
                val = - abs(left[i] - right[i])
            elif self.op.value == StlComparisonOperator.NEQ.value:
                val = abs(left[i] - right[i])
            elif self.op.value == StlComparisonOperator.LEQ.value or self.op.value == StlComparisonOperator.LESS.value:
                val = right[i] - left[i]
            elif self.op.value == StlComparisonOperator.GEQ.value or self.op.value == StlComparisonOperator.GREATER.value:
                val = left[i] - right[i]
            else:
                raise LTLException('Unknown predicate operation')
            out.append(val)

        return out

    def sat(self, left, right):
        out = []
        for i in range(len(left)):
            if self.op.value == StlComparisonOperator.EQ.value:
                val = left[i] == right[i]
            elif self.op.value == StlComparisonOperator.NEQ.value:
                val = left[i] != right[i]
            elif self.op.value == StlComparisonOperator.GEQ.value:
                val = left[i] >= right[i]
            elif self.op.value == StlComparisonOperator.GREATER.value:
                val = left[i] > right[i]
            elif self.op.value == StlComparisonOperator.LEQ.value:
                val = left[i] <= right[i]
            elif self.op.value == StlComparisonOperator.LESS.value:
                val = left[i] < right[i]
            else:
                raise LTLException('Unknown predicate operation')

            out.append(val)

        return out
