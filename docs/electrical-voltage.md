# Electrical voltage domains

On a finite connected copied network, `Source.voltage J alpha beta hc` is the harmonic extension of boundary data one at `beta` and zero at other vertices of `{alpha, beta}`. At coincident poles this extension is one throughout the network; simultaneous zero and one at that pole is impossible.

The manuscript uses disjoint nonempty terminal sets, whose contracted vertices are distinct. `Source.CurrentDomain.source_voltage` requires this distinctness. Unique existence of the complete zero/one and free-vertex harmonic specification precedes its choice; the specification is equivalent to equality with the chosen field. `source_voltage_eq_voltage` identifies it with the general boundary-data extension on this domain.

The reference network uses `Repair8.voltage`, with internally proved connectivity and distinct false/true terminals. Its full specification and uniqueness identify it with `CurrentDomain.source_voltage`. The original extension is zero outside D and one on P through the proved projection identities. Strict interior grounded splits likewise produce connected networks with distinct poles.

Energy sums each original copied edge once. Literal loops contribute zero, and parallel edges keep their identities. The grounded Green kernel is the unit-current Poisson solution. The round61 means theorem joins all-edge absolute conjugacy, signed boundary voltage and indicator means, and total mean equal to the grounded diagonal and original energy.

The registered BSST assumption requires distinct poles. Transport through `source_voltage_eq_voltage` preserves its normalized specification and uses the assumption; it does not prove that standard theorem. The historical claim of simultaneous zero/one values for the general constructor at coincident poles fails on that domain and is not used as a source characterization.

See the [source-domain module](../FiniteAvalanches/Electrical/Geometry/CurrentSourceVoltage.lean), [reference voltage](../FiniteAvalanches/Electrical/Reference/Voltage.lean), [actual-network transports](../FiniteAvalanches/Electrical/CurrentVoltageApplicability.lean), and [means theorem](../FiniteAvalanches/Electrical/Reference/BoundaryMeans.lean).
