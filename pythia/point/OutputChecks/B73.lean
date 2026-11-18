import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block73_checked : centerBlock 73 = true := by decide +kernel
#print axioms block73_checked
end PythiaCert.Output
