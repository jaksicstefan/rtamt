from rtamt.operation.abstract_operation import AbstractOperation

class XorOperation(AbstractOperation):
    def __init__(self):
        pass

    def update(self, left, right):
        out = []

        for i in range(len(left)):
            out_sample = abs(left[i] - right[i])
            out.append(out_sample)

        return out
