import collections
from rtamt.operation.abstract_operation import AbstractOperation

class AlwaysBoundedOperation(AbstractOperation):
    def __init__(self, begin, end):
        self.begin = begin
        self.end = end

    def update(self, samples):
        out = []
        self.buffer = collections.deque(maxlen=(self.end + 1))

        for i in range(self.end + 1):
            val = float("inf")
            self.buffer.append(val)

        for i in range(len(samples)-1, -1, -1):
            self.buffer.append(samples[i])
            out_sample = float("inf")
            for j in range(self.end-self.begin+1):
                out_sample = min(out_sample, self.buffer[j])
            out.append(out_sample)
        out.reverse()

        return out
