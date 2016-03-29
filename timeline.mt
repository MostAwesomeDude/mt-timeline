import "unittest" =~ [=> unittest]
import "lib/codec/utf8" =~ [=> UTF8 :DeepFrozen]
import "lib/json" =~ [=> JSON :DeepFrozen]
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
    # traceln(`initials=$initials`)

    # The final values.
    def finals :Set[Str] := [for k => v in (edges) if (v == [].asSet()) k].asSet()
    # traceln(`finals=$finals`)

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
            l.push(n)
            if (g.contains(n)) {g.removeKey(n)}
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
            # Let's find a proving cycle.
            def cycleHead := g.getKeys()[0]
            var marker := g[cycleHead].asList()[0]
            def tails := [].diverge()
            while (marker != cycleHead) {
                tails.push(marker)
                marker := g[marker].asList()[0]
            }
            throw(`Cycle in DAG:
                ${g.size()} labels left
                Example cycle: ${[cycleHead] + tails}
            `)
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
    # assert.equal(dag.finals(), ["d"].asSet())
    # Antichains aren't always this predictable, but this particular graph is
    # easy to do by hand.
    assert.equal(dag.antichains(),
        [["a"].asSet(), ["b", "c"].asSet(), ["d"].asSet()])

unittest([
    testDAGDiamond,
])

def quoteDot(s :Str) :Str as DeepFrozen:
    return `"${s.replace("\"", "\\\"")}"`

def dot(dag, charMap :Map[Str, List[Str]], name :Str) as DeepFrozen:
    var charEdges := [].asMap()
    for char => scenes in (charMap):
        # Construct each possible edge, and indicate that this character is
        # present on that edge.
        for i => scene in (scenes):
            if (i == 0):
                continue
            def k := [scenes[i - 1], scene]
            def s := charEdges.fetch(k, fn {[].asSet()})
            charEdges with= (k, s.with(char))
    traceln(`charEdges=$charEdges`)
    def edges := [for [k, v] in (dag.edgePairs()) {
        # Only show the label if there's exactly one character.
        def charEdge := charEdges.fetch([k, v], fn {[].asSet()}).asList()
        def attrs := switch (charEdge) {
            match [char] {traceln(`boom $k $v $char`); `[label=${quoteDot(char)}]`}
            match _ {""}
        }
        `${quoteDot(k)} -> ${quoteDot(v)} $attrs;`
    }]
    def antichains := [for ac in (dag.antichains())
                       `subgraph {
                          rank = same;
                          ${";".join([for a in (ac) quoteDot(a)])};
                        };`]
    return `digraph ${quoteDot(name)} {
        rankdir="LR";
        ${"".join(edges)}
        ${"".join(antichains)}
    }`

def main(argv, => makeFileResource, => unsealException) as DeepFrozen:
    def data := makeFileResource("timeline.json")<-getContents()
    return when (data) ->
        def via (UTF8.decode) via (JSON.decode) d := data
        traceln("Loaded JSON")

        var sceneMap := [].asMap()
        for char => scenes in (d):
            def [var scene] + tail exit __continue := scenes
            for target in (tail):
                def s :Set := sceneMap.fetch(scene, fn {[].asSet()})
                sceneMap with= (scene, s.with(target))
                scene := target
            if (!sceneMap.contains(scene)):
                sceneMap with= (scene, [].asSet())

        def dag := makeDAG(sceneMap)
        traceln("Valid DAG")

        def via (UTF8.encode) bs := dot(dag, d, "timeline")
        traceln("Produced DOT")

        def handle := makeFileResource("test.dot")
        when (handle<-setContents(bs)) -> {0}
