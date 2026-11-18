import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block151_checked : centerBlock 151 = true := by decide +kernel
#print axioms block151_checked
end PythiaCert.Output
