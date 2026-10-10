"""Independent decoder for the bounded logical-tree bytes in proof descriptors."""


def decode_tree(encoded):
    """The bounded logical tree encoding: tag 0 is a string, tag 1 a list."""
    def node(at):
        tag, count = encoded[at], int.from_bytes(encoded[at + 1:at + 9], 'little')
        at += 9
        if tag == 0:
            return encoded[at:at + count].decode(), at + count
        assert tag == 1
        items = []
        for _ in range(count):
            item, at = node(at)
            items.append(item)
        return items, at
    tree, end = node(0)
    assert end == len(encoded)
    return tree

