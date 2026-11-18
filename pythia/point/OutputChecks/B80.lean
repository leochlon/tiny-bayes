import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block80_checked : centerBlock 80 = true := by decide +kernel
#print axioms block80_checked
end PythiaCert.Output
