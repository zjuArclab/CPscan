


bool can_extend_graph
    (const GraphFirst& graph1,
     const GraphSecond& graph2,
     CorrespondenceMapFirstToSecond correspondence_map_1_to_2,
     CorrespondenceMapSecondToFirst /*correspondence_map_2_to_1*/,
     typename graph_traits<GraphFirst>::vertices_size_type subgraph_size,
     typename graph_traits<GraphFirst>::vertex_descriptor new_vertex1,
     typename graph_traits<GraphSecond>::vertex_descriptor new_vertex2,
     EdgeEquivalencePredicate edges_equivalent,
     VertexEquivalencePredicate vertices_equivalent,
     bool only_connected_subgraphs);


bool mcgregor_common_subgraphs_internal
    (const GraphFirst& graph1,
     const GraphSecond& graph2,
     const VertexIndexMapFirst& vindex_map1,
     const VertexIndexMapSecond& vindex_map2,
     CorrespondenceMapFirstToSecond correspondence_map_1_to_2,
     CorrespondenceMapSecondToFirst correspondence_map_2_to_1,
     VertexStackFirst& vertex_stack1,
     EdgeEquivalencePredicate edges_equivalent,
     VertexEquivalencePredicate vertices_equivalent,
     bool only_connected_subgraphs,
     SubGraphInternalCallback subgraph_callback);

inline void mcgregor_common_subgraphs_internal_init
    (const GraphFirst& graph1,
     const GraphSecond& graph2,
     const VertexIndexMapFirst vindex_map1,
     const VertexIndexMapSecond vindex_map2,
     EdgeEquivalencePredicate edges_equivalent,
     VertexEquivalencePredicate vertices_equivalent,
     bool only_connected_subgraphs,
     SubGraphInternalCallback subgraph_callback);