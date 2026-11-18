import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block114_checked : centerBlock 114 = true := by decide +kernel
#print axioms block114_checked
end PythiaCert.Output
