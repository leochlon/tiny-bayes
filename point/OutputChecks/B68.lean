import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block68_checked : centerBlock 68 = true := by decide +kernel
#print axioms block68_checked
end PythiaCert.Output
