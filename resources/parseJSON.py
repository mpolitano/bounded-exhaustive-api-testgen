import json
import os
 
path=os.environ.get('BE_EXP_SRC') 
# JSON string
file = open(path+"/inferFiles/report.json",)
fileResult = open(path+"/impure_methods.txt","w")
# Convert string to Python dict
data = json.load(file)
# print(data[3]['procedure'])
index = 0
for i in data:
    fileResult.write(data[index]["procedure"].rsplit(':', 1)[0]+'\n')
    index+=1


file.close()
fileResult.close()
