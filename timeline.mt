import "unittest" =~ [=> unittest]
import "lib/codec/utf8" =~ [=> UTF8 :DeepFrozen]
import "lib/tubes" =~ [
    => makeUTF8EncodePump :DeepFrozen,
    => makePumpTube :DeepFrozen,
]
exports (main)

def makeDAG(edges :Map[Str, Set[Str]]) as DeepFrozen:
    "Produce a directed acyclic graph.
    
     If the given graph is not acyclic, an exception is thrown."

    # Keys have outgoing edges; values have incoming edges.
    def keys :Set[Str] := edges.getKeys().asSet()
    def values :Set[Str] := {
        var s := [].asSet()
        for v in (edges.getValues()) {
            s |= v
        }
        s
    }

    # The initial values.
    def initials :Set[Str] := keys &! values

    # The final values.
    def finals :Set[Str] := [for k => v in (edges) if (v == [].asSet()) k].asSet()

    # A topologically-sorted linearization of this DAG. It witnesses the proof
    # that the DAG has no cycles. This version is known as Kahn's algorithm.
    def topoSorted :List[Str] := {
        def l := [].diverge()
        def s := finals.diverge()
        def g := edges.diverge()
        # For each node with no more incoming edges, push it onto the list and
        # cleave it from the graph.
        while (s.size() != 0) {
            def n := s.pop()
            if (g.contains(n)) {g.removeKey(n)}
            l.push(n)
            for m => labels in (g) {
                if (labels.contains(n)) {
                    if (labels.size() == 1) {
                        # n has the last edge to m; m can be cleaved.
                        g.removeKey(m)
                        s.include(m)
                    } else {
                        # Trim.
                        g[m] := labels.without(n)
                    }
                }
            }
        }
        if (g.size() != 0) {
            throw(`Cycle in DAG involving these labels: ${g.getKeys()}`)
        }
        l.snapshot().reverse()
    }

    return object directedAcyclicGraph as DeepFrozen:
        "A directed acyclic graph."

        to size() :Int:
            "The number of elements in this DAG."

            return (keys & values).size()

        to initials() :Set[Str]:
            "The elements in this DAG which do not have incoming edges."

            return initials

        to finals() :Set[Str]:
            "The elements in this DAG which do not have outgoing edges."

            return finals

        to topoSort() :List[Str]:
            "All elements in this DAG, topologically sorted."

            return topoSorted

        to edgePairs() :List[Pair[Str, Str]]:
            "All edges in this DAG, as pairs."

            def l := [].diverge()
            for k => vs in (edges):
                for v in (vs):
                    l.push([k, v])
            return l.snapshot()

        to antichains() :List[Set[Str]]:
            "The elements of the DAG decomposed into antichains."

            def l := [].diverge()
            def g := edges.diverge()
            traceln(`looking for antichains of $g`)
            while (g.size() != 0):
                def antichain := [for k => v in (g) if (v == [].asSet()) k].asSet()
                traceln(`antichain $antichain`)
                l.push(antichain)
                # Remove the nodes from the graph.
                for n in (antichain):
                    g.removeKey(n)
                # Trim the edges, exposing the next antichain.
                for k => v in (g):
                    g[k] := v - antichain
            return l.snapshot().reverse()

def testDAGDiamond(assert):
    def dag := makeDAG([
        "a" => ["b", "c"].asSet(),
        "b" => ["d"].asSet(),
        "c" => ["d"].asSet(),
        "d" => [].asSet(),
    ])
    assert.equal(dag.initials(), ["a"].asSet())
    assert.equal(dag.finals(), ["d"].asSet())
    # Antichains aren't always this predictable, but this particular graph is
    # easy to do by hand.
    assert.equal(dag.antichains(),
        [["a"].asSet(), ["b", "c"].asSet(), ["d"].asSet()])

unittest([
    testDAGDiamond,
])

def dot(dag, name :Str) as DeepFrozen:
    def lines := [for [k, v] in (dag.edgePairs()) `"$k" -> "$v";`]
    return `digraph "$name" {${"".join(lines)}}`

def writeDot(dag, name :Str, handle) as DeepFrozen:
    def via (UTF8.encode) bs := dot(dag, name)
    return handle<-setContents(bs)

def setupStdOut(makeStdOut) as DeepFrozen:
    def stdout := makePumpTube(makeUTF8EncodePump())
    stdout<-flowTo(makeStdOut())
    return stdout

def main(argv, => makeFileResource, => makeStdOut, => unsealException) as DeepFrozen:
    def stdout := setupStdOut(makeStdOut)
    stdout<-receive("Hi!\n")

    def dag := makeDAG([
        "a" => ["b", "c"].asSet(),
        "b" => ["d"].asSet(),
        "c" => ["d"].asSet(),
        "d" => ["e", "f"].asSet(),
        "e" => ["g"].asSet(),
        "f" => ["h"].asSet(),
        "g" => ["h", "i"].asSet(),
        "h" => [].asSet(),
        "i" => [].asSet(),
    ])
    traceln(dag)
    traceln(dag.topoSort())
    traceln(dag.antichains())
    traceln(dag.edgePairs())

    def handle := makeFileResource("test.dot")
    return when (writeDot(dag, "test", handle)) -> {0}
