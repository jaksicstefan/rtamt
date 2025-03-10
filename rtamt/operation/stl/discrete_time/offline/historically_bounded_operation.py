import collections
from rtamt.operation.abstract_operation import AbstractOperation

class HistoricallyBoundedOperation(AbstractOperation):
    def __init__(self, begin, end):
        self.begin = begin
        self.end = end

    def update(self, samples):
        out = []
        self.buffer = collections.deque(maxlen=(self.end + 1))

        for i in range(self.end + 1):
            val = float("inf")
            self.buffer.append(val)

        for sample in samples:
            self.buffer.append(sample)
            out_sample = float("inf")
            for i in range(self.end-self.begin+1):
                out_sample = min(out_sample, self.buffer[i])
            out.append(out_sample)

        return out
