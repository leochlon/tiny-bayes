import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block52_checked : centerBlock 52 = true := by decide +kernel
#print axioms block52_checked
end PythiaCert.Output
