import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block185_checked : centerBlock 185 = true := by decide +kernel
#print axioms block185_checked
end PythiaCert.Output
