products = []

for i in range(4):
    name = input(f&quot;Enter product {i+1} name: &quot;)
    price = int(input(f&quot;Enter price of {name}: &quot;))
    products.append([name, price])

print(&quot;\n----- BILL -----&quot;)

total = 0

for item in products:
    print(item[0], &quot;=&quot;, item[1])
    total += item[1]

print(&quot;----------------&quot;)
print(&quot;Total Bill =&quot;, total)
